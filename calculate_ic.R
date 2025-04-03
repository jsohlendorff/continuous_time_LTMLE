cumulative_hazard_cox <- function(m, dt, covariate_dt, times_dt, causes) {
  ## Find exp(LP)
  exp_lp_dt <- data.table(id = covariate_dt$id)
  base_hazard <- NULL
  for (j in causes) {
    exp_lp <- predict(m[[j]]$fit, newdata = covariate_dt, type = "risk", reference = "zero")
    exp_lp_dt[, paste0("exp_lp_", j) := exp_lp]
    ## Baseline hazard function
    if (is.null(base_hazard)) {
      base_hazard <- as.data.table(basehaz(m[[j]]$fit, centered = FALSE))
      setnames(base_hazard, "hazard",  paste0("hazard_", j))
    } else {
      base_hazard <- merge(base_hazard, as.data.table(basehaz(m[[j]]$fit, centered = FALSE)), by = "time")
      setnames(base_hazard, "hazard",  paste0("hazard_", j))
    }
    base_hazard[, paste0("hazard_minus_",j) := c(0, hazard_j[-.N]), env = list(hazard_j = paste0("hazard_", j))]
  }
  base_hazard <- base_hazard[times_dt, roll = TRUE, on = "time"]
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


influence_curve_censoring_martingale_time_varying <- function(dt,
                                                              learn_causes,
                                                              learn_censor,
                                                              cause = 1,
                                                              weight_fun = function(x)
                                                                1,
                                                              non_zero,
                                                              tau,
                                                              k) {
  ## TODO: Assume the data is on interevent form
  assertthat::assert_that(is.data.frame(dt))
  ## Assert that time is sorted
  assertthat::assert_that(all(diff(na.omit(dt$time)) >= 0))
  ## Omit observations with NAs in time and event

  dt <- dt[, time_prev := time_minus, env = list(time_minus = paste0("time_", k -
                                                                       1))]
  for (j in seq_len(k - 1)) {
    dt <- dt[, time_j := time_prev - time_j, env = list(time_j = paste0("time_", j))]
  }
  dt <- dt[, time := time - time_prev]

  my_covariate_dt <- copy(as.data.table(dt))
  my_covariate_dt <- my_covariate_dt[non_zero]
  times_to_use <- my_covariate_dt[, c("time", "event", "id")]
  setnames(times_to_use,
           c("time", "event", "id"),
           c("time_id", "event_id", "id"))
  my_covariate_dt <- my_covariate_dt[, -c("time", "event")]

  name_covariates <- copy(setdiff(colnames(my_covariate_dt), c("time_prev", "id")))
  if (k == 1)
    name_covariates <- setdiff(name_covariates, "time_0")
  my_times_dt <- as.data.table(dt)
  my_times_dt <- my_times_dt[event == cause, "time"]

  ## Get minimal prior event time
  ## here we should also subset so that <= tau - min_i T_(k-1)
  # min_T_k_1 <- my_times_dt[, min(time), by = id]
  # my_times_dt <- my_times_dt[time <= tau - min_T_k_1& event == 1]

  ## Cartesian product
  my_dt <- my_covariate_dt[, as.list(my_times_dt), by = my_covariate_dt]
  my_dt <- my_dt[time <= tau - time_prev] ## my_dt[,.N,by=id] different number of observationby id
  my_dt <- cumulative_hazard_cox(learn_causes, my_dt, my_covariate_dt, my_times_dt, names(learn_causes))
  ## apply the weight function to all other columns than id and F1
  ## TODO: the time columns should be shifted with T_(k-1), i.e., added; find "time", "time_(k-1), time_(k-2), dots, time_1" and add T_(k-1)
  setkey(my_dt, id, time)
  my_dt <- my_dt[, diff_Lambda_cause := diff(c(0, Lambda_cause)), by = id, env = list(Lambda_cause = paste0("Lambda_cause_", cause))]
  my_dt <- my_dt[, Sminus := 1]
  for (j in names(learn_causes)) {
    my_dt <- my_dt[, Sminus  := Sminus * exp(-Lambda_minus_x), env = list(Lambda_minus_x = paste0("Lambda_cause_minus_", j)), by = id]
  }
  ## Fix this later with L_1
  setnames(my_dt, "time", paste0("time_", k))
  my_dt <- my_dt[, new_event := cause, env = list(new_event = paste0("event_", k))]
  my_dt <- my_dt[, weight := weight_fun(.SD), .SDcols = c(name_covariates, paste0(c("time_", "event_"), k))]
  my_dt <- my_dt[, Q := cumsum(weight * Sminus * diff_Lambda_cause), by = id]

  my_dt[, c(
    "diff_Lambda_cause",
    paste0("Lambda_cause_", names(learn_causes)),
    "weight",
    "Sminus",
    paste0("Lambda_cause_minus_", names(learn_causes))
  ) := NULL]
  dt_Q_last <- my_dt[, .(Q_last = Q[.N]), by = id]
  setnames(my_dt, paste0(c("time_", "event_"), k), c("time", "event"))

  cens_dt <- dt[time <= tau - time_prev & event == "C", "time"]
  cens_dt_original <- copy(cens_dt)
  ## Cartesian product of cens_dt and my_covariate_dt
  cens_dt <- my_covariate_dt[, as.list(cens_dt), by = my_covariate_dt]

  ## rolling join (forward) to get Q at censoring times
  my_dt <- my_dt[cens_dt, roll = TRUE, on = c(name_covariates, "id", "time")]
  my_dt <- merge(my_dt, dt_Q_last, by = "id")
  my_dt[is.na(Q), Q := 0]

  ## predict cumulative hazard function
  learn_causes_with_censor <- learn_causes
  learn_causes_with_censor[["C"]]$fit <- learn_censor

  my_dt <- cumulative_hazard_cox(learn_causes_with_censor, my_dt, my_covariate_dt, cens_dt_original, names(learn_causes_with_censor))
  my_dt <- my_dt[, diff_Lambda_cause_C := diff(c(0, Lambda_cause_C)), by = id]
  my_dt <- my_dt[, Scu := exp(-Lambda_cause_C)]
  my_dt <- my_dt[, Su := 1]
  for (j in names(learn_causes)) {
    my_dt <- my_dt[, Su  :=  Su * exp(-Lambda_x), env = list(Lambda_x = paste0("Lambda_cause_", j)), by = id]
  }

  ## define Q_last as the last Q within each id
  my_dt <- merge(my_dt, times_to_use, by = "id")
  no_id_match  <- my_dt[, (sum(time <= time_id) == 0), by = "id"][V1 == TRUE, ]$id
  res2 <- my_dt[id %in% no_id_match, .(cens_mg = 0, Q = Q_last[.N]), by = id]
  my_dt <- my_dt[time <= time_id]

  # my_dt <- my_dt[time <= time_id]
  #

  res <- my_dt[, .(
    cens_mg =
      1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau - time_prev[.N] &
                                                             event_id[.N] == "C") - sum(1 / (Scu * Su) * (Q_last - Q) * diff_Lambda_cause_C),
    Q = Q_last[.N]
  ), by = id]
  res <- rbind(res, res2)
  setkey(res, id)
  res
  # my_dt[, .(
  #   cens_mg =
  #     1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau &
  #                                                            event_id[.N] == "C") - sum(1 / (Scu * Su) * (Q_last - Q) * diff_Lambda_cause_C)
  # ), by = id]
}
