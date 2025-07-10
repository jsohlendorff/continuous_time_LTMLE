## Function to calculate the cumulative hazard function for Cox models efficiently
## As such, covariate_data and times_data aren't needed as arguments, but the implementation is more
## computationally efficient for the Cox model here, since
## Lambda( t_j | x_i) = Lambda_0 (t_j) * exp(LP(x_i))
## so Lambda_0 (t_j) and exp(LP(x_i)) may be stored as vectors.
## The cumulative hazards are then obtained by taking a cartesian product.
cumulative_hazard_cox <- function(models, dt, covariate_data, times_data, causes) {
  ## Find exp(LP); i.e., exponential of linear predictor
  exp_lp_dt <- data.table(id = covariate_data$id)
  base_hazard <- NULL
  for (j in causes) {
    ## Predict linear predictor for each cause, i.e., exp(LP (X_j)) for all covariates X_j
    exp_lp <- predict(models[[j]]$fit, newdata = covariate_data, type = "risk", reference = "zero")
    exp_lp_dt[, paste0("exp_lp_", j) := exp_lp]
    ## Baseline cumulative hazard Lambda_0^x (T_j) for all j
    if (is.null(base_hazard)) {
      base_hazard <- as.data.table(basehaz(models[[j]]$fit, centered = FALSE))
      setnames(base_hazard, "hazard", paste0("hazard_", j))
    } else {
      base_hazard <- merge(base_hazard, as.data.table(basehaz(models[[j]]$fit, centered = FALSE)), by = "time")
      setnames(base_hazard, "hazard", paste0("hazard_", j))
    }
    ## Baseline cumulative hazard Lambda_0^x (T_j-) for all j
    base_hazard[, paste0("hazard_minus_", j) := c(0, hazard_j[-.N]), env = list(hazard_j = paste0("hazard_", j))]
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

# Influence curve for the censoring martingale
influence_curve_censoring_martingale <- function(dt,
                                                 learn_causes,
                                                 learn_censor,
                                                 cause = 1,
                                                 non_zero,
                                                 tau,
                                                 k,
                                                 tilde_nu,
                                                 static_intervention) {
  dt <- copy(dt)
  assertthat::assert_that(is.data.frame(dt))
  ## Assert that time is sorted
  assertthat::assert_that(all(diff(na.omit(dt$time)) >= 0))
  ## Change time to interarrival time
  dt <- dt[, time_prev := time_minus, env = list(time_minus = paste0("time_", k -
    1))]
  for (j in seq_len(k - 1)) {
    dt <- dt[, time_j := time_prev - time_j, env = list(time_j = paste0("time_", j))]
  }
  dt <- dt[, time := time - time_prev]

  ## Set covariate data = prior history (i.e., all covariates before time k)
  covariate_data <- copy(as.data.table(dt))
  covariate_data <- covariate_data[non_zero]
  time_id_data <- covariate_data[, c("time", "event", "id")] ## for keeping track about whether t <= T_i and tau in MG calculation
  setnames(
    time_id_data,
    c("time", "event", "id"),
    c("time_id", "event_id", "id")
  )
  covariate_data <- covariate_data[, -c("time", "event")]

  name_covariates <- setdiff(colnames(covariate_data), c("time_prev", "id"))
  if (k == 1) {
    name_covariates <- setdiff(name_covariates, "time_0")
  }

  ## Cause-specific event times
  times_data <- as.data.table(dt)
  times_data <- times_data[event == cause, "time"]

  ## Cartesian product to get all combinations of covariates and times for the computation of mu.
  pooled_data <- covariate_data[, as.list(times_data), by = covariate_data]

  ## Get minimal prior event time
  ## here we should also subset so that <= tau - min_i T_((k-1),i) (interarrival scale)
  pooled_data <- pooled_data[time <= tau - time_prev]

  ## Get estimates of cumulative hazard for mu computation
  ## TODO: add other possibilities for censoring.
  ## These should for all causes return predicted values of the cumulative hazard
  ## for each row of pooled_data (corresponding to each time x covariate combination)
  ## NOTE: Should be possible with predictRisk from riskRegression
  pooled_data <- cumulative_hazard_cox(
    learn_causes,
    pooled_data,
    covariate_data,
    times_data,
    names(learn_causes)
  )

  setkey(pooled_data, id, time)
  pooled_data <- pooled_data[, Delta_Lambda_cause := diff(c(0, Lambda_cause)), by = id, env = list(Lambda_cause = paste0("Lambda_cause_", cause))]
  pooled_data <- pooled_data[, Sminus := 1]
  for (j in names(learn_causes)) {
    pooled_data <- pooled_data[, Sminus := Sminus * exp(-Lambda_minus_x), env = list(Lambda_minus_x = paste0("Lambda_cause_minus_", j)), by = id]
  }
  setnames(pooled_data, "time", paste0("time_", k))
  pooled_data <- pooled_data[, new_event := cause, env = list(new_event = paste0("event_", k))]

  ## Predict from prior regressions
  if (!is.null(tilde_nu)) {
    pooled_data <- pooled_data[, weight := predict_intervention(.SD, k, tilde_nu, static_intervention), .SDcols = c(name_covariates, paste0(c("time_", "event_"), k))]
  } else {
    pooled_data <- pooled_data[, weight := 1]
  }

  ## Check for very large weights. These should be between 0 and 1! Inform user for badly behaved models.
  if (any(pooled_data$weight > 100)) {
    warning("Some weights are larger than 100. Truncating as weights are supposed to be probabilities ...")
    ## Calculate percentage of weights larger than 100
    percentage_large_weights <- sum(pooled_data$weight > 100) / nrow(pooled_data) * 100
    message(paste0("Percentage of weights larger than 100: ", round(percentage_large_weights, 3), "%"))
    pooled_data[weight > 100, weight := 100]
  }

  ## mu computation along all event times (Equation 26)
  ##  mu_k (u | h(k)) = integral_(T(k))^(u) prodint2(s, T(k), u) (1-sum_(x=a,l,d,y) Lambda_(k)^x (dif s | H(k))) \
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

  ## Censored times
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
    pooled_data <- pooled_data[, Su := Su * exp(-Lambda_x), env = list(Lambda_x = paste0("Lambda_cause_", j)), by = id]
  }

  pooled_data <- merge(pooled_data, time_id_data, by = "id")

  # If all censoring times occur after the event time; then cens_mg = 0
  no_id_match <- pooled_data[, (sum(time <= time_id) == 0), by = "id"][V1 == TRUE, ]$id
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
