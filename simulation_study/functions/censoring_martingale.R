## Function to calculate the cumulative hazard function for Cox models efficiently
cumulative_hazard_cox <- function(m, dt, covariate_dt, times_data, causes) {
  ## Find exp(LP); i.e., exponential of linear predictor
  exp_lp_dt <- data.table(id = covariate_dt$id)
  base_hazard <- NULL
  for (j in causes) {
    ## Predict linear predictor for each cause, i.e., exp(LP (X_j)) for all covariates X_j
    exp_lp <- predict(m[[j]]$fit, newdata = covariate_dt, type = "risk", reference = "zero")
    exp_lp_dt[, paste0("exp_lp_", j) := exp_lp]
    ## Baseline cumulative hazard Lambda_0^x (T_j) for all j
    if (is.null(base_hazard)) {
      base_hazard <- as.data.table(basehaz(m[[j]]$fit, centered = FALSE))
      setnames(base_hazard, "hazard",  paste0("hazard_", j))
    } else {
      base_hazard <- merge(base_hazard, as.data.table(basehaz(m[[j]]$fit, centered = FALSE)), by = "time")
      setnames(base_hazard, "hazard",  paste0("hazard_", j))
    }
    ## Baseline cumulative hazard Lambda_0^x (T_j-) for all j
    base_hazard[, paste0("hazard_minus_",j) := c(0, hazard_j[-.N]), env = list(hazard_j = paste0("hazard_", j))]
  }
  
  ## Merge/roll forward and calculate cumulative hazard function
  base_hazard <- base_hazard[times_data, roll = TRUE, on = "time"]
  dt <- merge(dt, base_hazard, by = "time")
  dt <- merge(dt, exp_lp_dt, by = "id")
  for (j in causes) {
    dt[, paste0("Lambda_cause_", j) := exp_lp_j * hazard_j, env = list(exp_lp_j = paste0("exp_lp_", j), hazard_j = paste0("hazard_", j))]
    dt[, paste0("Lambda_cause_minus_", j) := exp_lp_j * hazard_minus_j, env = list(exp_lp_j = paste0("exp_lp_", j), hazard_minus_j = paste0("hazard_minus_", j))]
  }
  names_to_remove <- c(sapply(causes, function(x) c(paste0("exp_lp_", x), paste0("hazard_", x), paste0("hazard_minus_", x))))
  dt[, (names_to_remove) := NULL]
  dt
}

#' Influence curve for the censoring martingale
influence_curve_censoring_martingale <- function(dt,
                                                 learn_causes,
                                                 learn_censor,
                                                 cause = 1,
                                                 non_zero,
                                                 tau,
                                                 k,
                                                 tilde_nu,
                                                 static_intervention) {
  ## TODO: Assume the data is on interevent form
  assertthat::assert_that(is.data.frame(dt))
  ## Assert that time is sorted
  assertthat::assert_that(all(diff(na.omit(dt$time)) >= 0))
  ## Shift time to interarrival time
  dt <- dt[, time_prev := time_minus, env = list(time_minus = paste0("time_", k -
                                                                       1))]
  for (j in seq_len(k - 1)) {
    dt <- dt[, time_j := time_prev - time_j, env = list(time_j = paste0("time_", j))]
  }
  dt <- dt[, time := time - time_prev]
  
  covariate_data <- copy(as.data.table(dt))
  covariate_data <- covariate_data[non_zero]
  times_to_use <- covariate_data[, c("time", "event", "id")]
  setnames(times_to_use,
           c("time", "event", "id"),
           c("time_id", "event_id", "id"))
  covariate_data <- covariate_data[, -c("time", "event")]
  
  name_covariates <- setdiff(colnames(covariate_data), c("time_prev", "id"))
  if (k == 1)
    name_covariates <- setdiff(name_covariates, "time_0")
  times_data <- as.data.table(dt)
  times_data <- times_data[event == cause, "time"]
  
  ## Get minimal prior event time
  ## here we should also subset so that <= tau - min_i T_((k-1),i) (interarrival scale)
  # min_T_k_1 <- times_data[, min(time), by = id]
  # times_data <- times_data[time <= tau - min_T_k_1& event == 1]
  
  ## Cartesian product to get all combinations of covariates and times for the computation of mu.
  pooled_data <- covariate_data[, as.list(times_data), by = covariate_data]
  pooled_data <- pooled_data[time <= tau - time_prev]
  ## Get estimates of cumulative hazard for mu computation
  pooled_data <- cumulative_hazard_cox(learn_causes,
                                       pooled_data,
                                       covariate_data,
                                       times_data,
                                       names(learn_causes))
  
  setkey(pooled_data, id, time)
  pooled_data <- pooled_data[, Delta_Lambda_cause := diff(c(0, Lambda_cause)), by = id, env = list(Lambda_cause = paste0("Lambda_cause_", cause))]
  pooled_data <- pooled_data[, Sminus := 1]
  for (j in names(learn_causes)) {
    pooled_data <- pooled_data[, Sminus  := Sminus * exp(-Lambda_minus_x), env = list(Lambda_minus_x = paste0("Lambda_cause_minus_", j)), by = id]
  }
  setnames(pooled_data, "time", paste0("time_", k))
  pooled_data <- pooled_data[, new_event := cause, env = list(new_event = paste0("event_", k))]
  if (!is.null(tilde_nu)) {
    pooled_data <- pooled_data[, weight := predict_intervention(.SD, k, tilde_nu, static_intervention), .SDcols = c(name_covariates, paste0(c("time_", "event_"), k))]
  } else {
    pooled_data <- pooled_data[, weight := 1]
  }
  ## mu computation along all event times
  ##  mu_k (u | h(k)) &= integral_(T(k))^(u) prodint2(s, T(k), u) (1-sum_(x=a,l,d,y) Lambda_(k)^x (dif s | H(k))) \
  ## quad times [Lambda^y_(k+1) (dif s | H(k)) + bb(1) {s < u} tilde(nu)_(k+1,tau)(1, s, a, H(k)) Lambda^a_(k+1) (dif s | historycensored(k))
  ## + bb(1) {s < u} tilde(nu)_(k+1, tau)(A(k-1), s, ell, H(k)) Lambda^ell_(k+1) (dif s | H(k))].
  pooled_data <- pooled_data[, mu := cumsum(weight * Sminus * Delta_Lambda_cause), by = id]
  
  pooled_data[, c(
    "Delta_Lambda_cause",
    paste0("Lambda_cause_", names(learn_causes)),
    "weight",
    "Sminus",
    paste0("Lambda_cause_minus_", names(learn_causes))
  ) := NULL]
  mu_tau_data <- pooled_data[, .(mu_tau = mu[.N]), by = id]
  setnames(pooled_data, paste0(c("time_", "event_"), k), c("time", "event"))
  
  censoring_times <- dt[time <= tau - time_prev &
                          event == "C", "time"]
  censoring_times_original <- copy(censoring_times)
  ## Cartesian product of censoring_times and covariate_data
  censoring_times <- covariate_data[, as.list(censoring_times), by = covariate_data]
  
  ## rolling join (forward) to get mu at censoring times
  pooled_data <- pooled_data[censoring_times, roll = TRUE, on = c(name_covariates, "id", "time")]
  pooled_data <- merge(pooled_data, mu_tau_data, by = "id")
  pooled_data[is.na(mu), mu := 0]
  
  ## predict cumulative hazard function
  learn_causes_with_censor <- learn_causes
  learn_causes_with_censor[["C"]]$fit <- learn_censor
  
  pooled_data <- cumulative_hazard_cox(
    learn_causes_with_censor,
    pooled_data,
    covariate_data,
    censoring_times_original,
    names(learn_causes_with_censor)
  )
  pooled_data <- pooled_data[, Delta_Lambda_cause_C := diff(c(0, Lambda_cause_C)), by = id] ## increments for integral
  pooled_data <- pooled_data[, Scu := exp(-Lambda_cause_C)] ## tilde(S^c) (u)
  pooled_data <- pooled_data[, Su := 1] ## S (u)
  for (j in names(learn_causes)) {
    pooled_data <- pooled_data[, Su  :=  Su * exp(-Lambda_x), env = list(Lambda_x = paste0("Lambda_cause_", j)), by = id]
  }

  ## define mu_tau as the last mu within each id
  pooled_data <- merge(pooled_data, times_to_use, by = "id")
  no_id_match  <- pooled_data[, (sum(time <= time_id) == 0), by = "id"][V1 == TRUE, ]$id ## If all censoring times occur after the event time; then cens_mg = 0
  result_no_match <- pooled_data[id %in% no_id_match, .(cens_mg = 0, mu = mu_tau[.N]), by = id]
  pooled_data <- pooled_data[time <= time_id]
  
  ## Censoring martingale of Equation 25
  res <- pooled_data[, .(
    cens_mg =
      1 / (Scu[.N] * Su[.N]) * (mu_tau[.N] - mu[.N]) * 1 * (time_id[.N] <= tau - time_prev[.N] &
                                                              event_id[.N] == "C") - sum(1 / (Scu * Su) * (mu_tau - mu) * Delta_Lambda_cause_C),
    mu = mu_tau[.N]
  ), by = id]
  res <- rbind(res, result_no_match)
  setkey(res, id)
  res
}
