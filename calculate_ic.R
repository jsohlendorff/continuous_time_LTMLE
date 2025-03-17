cumulative_hazard_cox <- function(m, dt, covariate_dt, times_dt, cause) {
  ## Find exp(LP)
  exp_lp <- predict(m, newdata = covariate_dt, type = "risk", reference = "zero")
  exp_lp <- data.table(id = covariate_dt$id, exp_lp =  exp_lp)
  ## Baseline hazard function
  base_hazard <- as.data.table(basehaz(m, centered = FALSE))
  base_hazard[, hazard_minus := c(0, hazard[-.N])]
  base_hazard <- base_hazard[times_dt, roll = TRUE, on = "time"]

  dt <- merge(dt, base_hazard, by = "time")
  dt <- merge(dt, exp_lp, by = "id")
  dt[, paste0("Lambda_cause_", cause) := exp_lp * hazard]
  dt[, paste0("Lambda_cause_minus_", cause) := exp_lp * hazard_minus]
  dt[, c("hazard", "exp_lp", "hazard_minus") := NULL]
  dt
}

influence_curve_censoring_martingale_time_varying <- function(dt,
                                                              m_event,
                                                              m_censor,
                                                              cause = 1,
                                                              weight_fun = function(x)
                                                                1,
                                                              treatment = 1,
                                                              tau = 6,
                                                              time_grid_primary_cause = NULL,
                                                              #TODO: add ability for smaller time grids
                                                              time_grid_censoring = NULL) {
  ## TODO: Assume the data is on interevent form
  assertthat::assert_that(is.data.frame(dt))
  ## Assert that time is sorted
  assertthat::assert_that(all(diff(dt$time) >= 0))
  
  my_covariate_dt <- as.data.table(dt)
  my_covariate_dt[, id := 1:.N]
  my_covariate_dt <- my_covariate_dt[X1 == "T1"]
  times_to_use <- my_covariate_dt[, c("time", "event", "id")]
  setnames(times_to_use,
           c("time", "event", "id"),
           c("time_id", "event_id", "id"))
  my_covariate_dt <- my_covariate_dt[, -c("time", "event")]
  
  name_covariates <- copy(colnames(my_covariate_dt))
  
  my_times_dt <- as.data.table(dt)
  my_times_dt <- my_times_dt[time <= tau & event == 1, "time"]
  
  ## Get minimal prior event time
  ## here we should also subset so that <= tau - min_i T_(k-1)
  # min_T_k_1 <- my_times_dt[, min(time), by = id]
  # my_times_dt <- my_times_dt[time <= tau - min_T_k_1& event == 1]
  
  ## Cartesian product
  my_dt <- my_covariate_dt[, as.list(my_times_dt), by = my_covariate_dt]

  my_dt <- cumulative_hazard_cox(m_event$models[[1]], my_dt, my_covariate_dt, my_times_dt, 1)
  my_dt <- cumulative_hazard_cox(m_event$models[[2]], my_dt, my_covariate_dt, my_times_dt, 2)
  
  ## apply the weight function to all other columns than id and F1
  ## TODO: the time columns should be shifted with T_(k-1), i.e., added; find "time", "time_(k-1), time_(k-2), dots, time_1" and add T_(k-1)
  setkey(my_dt, id, time)
  my_dt <- my_dt[, diff_Lambda_cause_1 := diff(c(0, Lambda_cause_1)), by = id]
  my_dt <- my_dt[, Sminus := exp(-Lambda_cause_minus_1 - Lambda_cause_minus_2), by = id]
  my_dt <- my_dt[, weight := weight_fun(.SD), .SDcols = c(name_covariates, "time")]
  my_dt <- my_dt[, Q := cumsum(weight * Sminus * diff_Lambda_cause_1), by = id]
  my_dt[, c(
    "diff_Lambda_cause_1",
    "Lambda_cause_1",
    "Lambda_cause_2",
    "weight",
    "Sminus",
    "Lambda_cause_minus_1",
    "Lambda_cause_minus_2"
  ) := NULL]
  cens_dt <- dt[time <= tau & event == 0, "time"]
  cens_dt_original <- copy(cens_dt)
  ## Cartesian product of cens_dt and my_covariate_dt
  
  cens_dt <- my_covariate_dt[, as.list(cens_dt), by = my_covariate_dt]
  
  ## rolling join (forward) to get Q at censoring times
  my_dt <- my_dt[cens_dt, roll = TRUE, on = c(name_covariates, "time")]
  my_dt[is.na(Q), Q := 0]
  
  ## predict cumulative hazard function
  my_dt <- cumulative_hazard_cox(m_censor, my_dt, my_covariate_dt, cens_dt_original, 0)
  my_dt <- my_dt[, diff_Lambda_cause_0 := diff(c(0, Lambda_cause_0)), by = id]
  my_dt <- cumulative_hazard_cox(m_event$models[[1]], my_dt, my_covariate_dt, cens_dt_original, 1)
  my_dt <- cumulative_hazard_cox(m_event$models[[2]], my_dt, my_covariate_dt, cens_dt_original, 2)
  my_dt <- my_dt[, Scu := exp(-Lambda_cause_0)]
  my_dt <- my_dt[, Su :=  exp(-(Lambda_cause_1 + Lambda_cause_2))]
  
  ## define Q_last as the last Q within each id
  my_dt <- my_dt[, Q_last := Q[.N], by = id]
  my_dt <- merge(my_dt, times_to_use, by = "id")
  my_dt <- my_dt[time <= time_id]
  
  my_dt[, .(cens_mg = 
    1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau & event_id[.N] == 0) - sum(1 / (Scu * Su) * (Q_last - Q) * diff_Lambda_cause_0),
  Q = Q_last[.N]), by = id]
}

## NOTE: should figure out why higher sample size leads to unstable estimates.
simulate <- function(n = 1000, tau = 6) {
  dt <- sampleData(
    n,
    outcome = "competing.risks",
    formula = ~ f(X1, 1) +
      f(X2, -0.033) + f(X3, 0.4) + f(X6, 0.1) + f(X7, -0.1) + f(X8, 0.5) + f(X9, -1)
  )
  levels(dt$X1) <- c("T0", "T1")
  df <- dt[order(dt$time), ]
  df[, c("eventtime1", "eventtime2", "censtime") := NULL]
  
  m.event <-  CSC(Hist(time, event) ~ X1 + X2 + X3 + X5 + X8, data = df)
  m.censor <-  coxph(
    Surv(time, event == 0) ~ X1 + X2 + X3 + X5 + X8,
    data = df,
    x = TRUE,
    y = TRUE
  )
  m.treatment <-  glm(X1 ~ X2 + X3 + X5 + X8,
                      data = df,
                      family = binomial(link = "logit"))
   mg <- influence_curve_censoring_martingale_time_varying(
    df,
    m_event = m.event,
    m_censor = m.censor,
    treatment = 1
  )

  ## merge with dt; for those ids not in mg, set cens_mg to 0
  df[, id := 1:.N]
  df <- merge(df, mg, by = "id", all.x = TRUE)
  df[is.na(cens_mg), c("cens_mg", "Q") := 0]
  
  # censoring_survival_predict <- predict(m_censor, type = "survival")
  # treatment_predict <- predict(mce.treatment, type = "response")
  df[, propensity_score := predict(m.treatment, type = "response")]
  df[, censoring_survival_predict := predict(m.censor, type = "survival")]
  df[, ic := 1 * (X1 == "T1") / propensity_score * ((1 * (time <= tau &
                                                            event == 1) / censoring_survival_predict) - Q + cens_mg)]
  df$X1 <- "T1"
  df[, F1tau := predictRisk(m.event,
                            newdata = .SD,
                            times = tau,
                            cause = 1)]
  df[, ic := ic + F1tau - mean(F1tau)]
  df[, .(
    estimate = mean(F1tau) + mean(ic),
    lower_ci = mean(F1tau) + mean(ic) - 1.96 * sd(ic) / sqrt(.N),
    upper_ci = mean(F1tau) + mean(ic) + 1.96 * sd(ic) / sqrt(.N)
  )]
}
