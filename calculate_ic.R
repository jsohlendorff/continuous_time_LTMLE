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

influence_curve_censoring_martingale <- function(dt,
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
  my_dt <- my_dt[, Q_last := Q[.N], by = id]
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
  my_dt <- merge(my_dt, times_to_use, by = "id")
  no_id_match  <- my_dt[, (sum(time <= time_id) == 0), by = "id"][V1 == TRUE, ]$id
  res2 <- my_dt[id %in% no_id_match, .(cens_mg = 0, Q = Q_last[.N]), by = id]
  my_dt <- my_dt[time <= time_id]

  # my_dt[, .(cens_mg =
  #   1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau & event_id[.N] == 0) - sum(1 / (Scu * Su) * (Q_last - Q) * diff_Lambda_cause_0),
  # Q = Q_last[.N]), by = id]
  res <- my_dt[, .(
    cens_mg =
      1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau &
                                                             event_id[.N] == 0) - sum(1 / (Scu * Su) * (Q_last - Q) * diff_Lambda_cause_0),
  ), by = id]
  rbind(res, res2)
}

## NOTE: should figure out why higher sample size leads to unstable estimates.
simulate <- function(n = 1000, tau = 6, conservative=FALSE, ate_fun =FALSE) {
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
  if (ate_fun){
    ateRobust3 <- ate(event = m.event,
                      treatment = m.treatment,
                      censor = m.censor,
                      estimator = c("AIPTW"),
                      data = df, times = tau,
                    cause = 1, se = TRUE,verbose=FALSE)
    res_ate<- ateRobust3$meanRisk[treatment=="T1", c("estimate", "se","lower","upper")]
    setnames(res_ate, c("estimate","lower", "se","upper"), c("estimate_ate", "se_ate","lower_ate","upper_ate"))
  } else {
    res_ate <- NULL
  }
  map_X1_to_T1 <- function(dt){
    dt$X1 <- "T1"
    dt
  }

  if (!conservative){
    mg <- influence_curve_censoring_martingale(
      df,
      m_event = m.event,
      m_censor = m.censor,
      treatment = 1
    )
    ## merge with dt; for those ids not in mg, set cens_mg to 0
    df[, id := 1:.N]
    df <- merge(df, mg, by = "id", all.x = TRUE)
    df[is.na(cens_mg), c("cens_mg", "Q") := 0]
  } else  {
    df[, cens_mg := 0]
  }
  df[, propensity_score := predict(m.treatment, type = "response")]
  df[, censoring_survival_predict := predict(m.censor, type = "survival")]
  df[, F1tau := predictRisk(m.event,
                            newdata = map_X1_to_T1(.SD),
                            times = tau,
                            cause = 1)]
  df[, ic := 1 * (X1 == "T1") / propensity_score * ((1 * (time <= tau &
                                                            event == 1) / censoring_survival_predict) - F1tau + cens_mg)]
  df[, ic_cons := 1 * (X1 == "T1") / propensity_score * ((1 * (time <= tau &
                                                            event == 1) / censoring_survival_predict) - F1tau)]
  df[, ic := ic + F1tau - mean(F1tau)]
  df[, ic_cons := ic_cons + F1tau - mean(F1tau)]

  res <- df[, .(
    estimate = mean(F1tau) + mean(ic),
    se = sd(ic) / sqrt(.N),
    lower_ci = mean(F1tau) + mean(ic) - 1.96 * sd(ic) / sqrt(.N),
    upper_ci = mean(F1tau) + mean(ic) + 1.96 * sd(ic) / sqrt(.N),
    estimate_cons = mean(F1tau) + mean(ic_cons),
    se_cons = sd(ic_cons) / sqrt(.N),
    lower_ci_cons = mean(F1tau) + mean(ic_cons) - 1.96 * sd(ic_cons) / sqrt(.N),
    upper_ci_cons = mean(F1tau) + mean(ic_cons) + 1.96 * sd(ic_cons) / sqrt(.N),
    g_formula_estimate = mean(F1tau)
  )]
  ## add ate
  res <- cbind(res, res_ate)
}

test_brice <- function(d, tau){
  df <- widen_continuous_data(d)$d_wide
  df <- df[order(df$time_1), ]

  levels(df$event_1) <- c(3,4,0,1,2)
  df$event_1 <- as.numeric(as.character(df$event_1))
  df$A_0 <- factor(df$A_0, levels = c(0,1))
  m.treatment <-  glm(A_0 ~ L_0,
                      data = df,
                      family = binomial(link = "logit"))
  m.event <-  CSC(Hist(time_1, event_1) ~ A_0+L_0, data = df)
  m.censor <-  coxph(
    Surv(time_1, event_1 == 0) ~ A_0+L_0,
    data = df,
    x = TRUE,
    y = TRUE
  )
  ate(event = m.event,
      treatment = m.treatment,
      censor = m.censor,
      data = df, times = tau,
      cause = 1)$meanRisk[treatment=="1", c("estimate", "se","lower","upper")]

}

# test_me <- function(d, tau, conservative = FALSE) {
#   influence_curve_censoring_martingale_test <- function(dt,
#                                                    m_event,
#                                                    m_censor,
#                                                    cause = 1,
#                                                    weight_fun = function(x)
#                                                      1,
#                                                    treatment = 1,
#                                                    tau = 6,
#                                                    time_grid_primary_cause = NULL,
#                                                    #TODO: add ability for smaller time grids
#                                                    time_grid_censoring = NULL) {
#     ## TODO: Assume the data is on interevent form
#     assertthat::assert_that(is.data.frame(dt))
#     ## Assert that time is sorted
#     assertthat::assert_that(all(diff(dt$time) >= 0))
#
#     my_covariate_dt <- as.data.table(dt)
#     my_covariate_dt <- my_covariate_dt[A_0 == 1]
#     times_to_use <- my_covariate_dt[, c("time", "event", "id")]
#     setnames(times_to_use,
#              c("time", "event", "id"),
#              c("time_id", "event_id", "id"))
#     my_covariate_dt <- my_covariate_dt[, -c("time", "event")]
#
#     name_covariates <- copy(colnames(my_covariate_dt))
#
#     my_times_dt <- as.data.table(dt)
#     my_times_dt <- my_times_dt[time <= tau & event == 1, "time"]
#
#     ## Get minimal prior event time
#     ## here we should also subset so that <= tau - min_i T_(k-1)
#     # min_T_k_1 <- my_times_dt[, min(time), by = id]
#     # my_times_dt <- my_times_dt[time <= tau - min_T_k_1& event == 1]
#
#     ## Cartesian product
#     my_dt <- my_covariate_dt[, as.list(my_times_dt), by = my_covariate_dt]
#
#     my_dt <- cumulative_hazard_cox(m_event$models[[1]], my_dt, my_covariate_dt, my_times_dt, 1)
#     my_dt <- cumulative_hazard_cox(m_event$models[[2]], my_dt, my_covariate_dt, my_times_dt, 2)
#
#     ## apply the weight function to all other columns than id and F1
#     ## TODO: the time columns should be shifted with T_(k-1), i.e., added; find "time", "time_(k-1), time_(k-2), dots, time_1" and add T_(k-1)
#     setkey(my_dt, id, time)
#     my_dt <- my_dt[, diff_Lambda_cause_1 := diff(c(0, Lambda_cause_1)), by = id]
#     my_dt <- my_dt[, Sminus := exp(-Lambda_cause_minus_1 - Lambda_cause_minus_2), by = id]
#     my_dt <- my_dt[, weight := weight_fun(.SD), .SDcols = c(name_covariates, "time")]
#     my_dt <- my_dt[, Q := cumsum(weight * Sminus * diff_Lambda_cause_1), by = id]
#     my_dt[, c(
#       "diff_Lambda_cause_1",
#       "Lambda_cause_1",
#       "Lambda_cause_2",
#       "weight",
#       "Sminus",
#       "Lambda_cause_minus_1",
#       "Lambda_cause_minus_2"
#     ) := NULL]
#     my_dt <- my_dt[, Q_last := Q[.N], by = id]
#     cens_dt <- dt[time <= tau & event == 0, "time"]
#     cens_dt_original <- copy(cens_dt)
#     ## Cartesian product of cens_dt and my_covariate_dt
#
#     cens_dt <- my_covariate_dt[, as.list(cens_dt), by = my_covariate_dt]
#
#     ## rolling join (forward) to get Q at censoring times
#     my_dt <- my_dt[cens_dt, roll = TRUE, on = c(name_covariates, "time")]
#     my_dt[is.na(Q), Q := 0]
#
#     ## predict cumulative hazard function
#     my_dt <- cumulative_hazard_cox(m_censor, my_dt, my_covariate_dt, cens_dt_original, 0)
#     my_dt <- my_dt[, diff_Lambda_cause_0 := diff(c(0, Lambda_cause_0)), by = id]
#     my_dt <- cumulative_hazard_cox(m_event$models[[1]], my_dt, my_covariate_dt, cens_dt_original, 1)
#     my_dt <- cumulative_hazard_cox(m_event$models[[2]], my_dt, my_covariate_dt, cens_dt_original, 2)
#     my_dt <- my_dt[, Scu := exp(-Lambda_cause_0)]
#     my_dt <- my_dt[, Su :=  exp(-(Lambda_cause_1 + Lambda_cause_2))]
#
#     ## define Q_last as the last Q within each id
#     my_dt <- merge(my_dt, times_to_use, by = "id")
#     my_dt <- my_dt[time <= time_id]
#
#     my_dt[, .(cens_mg =
#                 1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau & event_id[.N] == 0) - sum(1 / (Scu * Su) * (Q_last - Q) * diff_Lambda_cause_0),
#               Q = Q_last[.N]), by = id]
#   }
#
#   df <- widen_continuous_data(d)$d_wide
#   df <- df[order(df$time_1), ]
#
#   levels(df$event_1) <- c(3,4,0,1,2)
#   df$event_1 <- as.numeric(as.character(df$event_1))
#
#   m.event <-  CSC(Hist(time_1, event_1) ~ A_0+L_0, data = df)
#   m.censor <-  coxph(
#     Surv(time_1, event_1 == 0) ~ A_0+L_0,
#     data = df,
#     x = TRUE,
#     y = TRUE
#   )
#   m.treatment <-  glm(A_0 ~ L_0,
#                       data = df,
#                       family = binomial(link = "logit"))
#   # browser()
#   # dd <- copy(df)
#   # dd$A_0 <- factor(dd$A_0, levels = c(0,1))
#   # m.treatment <-  glm(A_0 ~ L_0,
#   #                     data = dd,
#   #                     family = binomial(link = "logit"))
#   # m.event <-  CSC(Hist(time_1, event_1) ~ A_0+L_0, data = dd)
#   # m.censor <-  coxph(
#   #   Surv(time_1, event_1 == 0) ~ A_0+L_0,
#   #   data = dd,
#   #   x = TRUE,
#   #   y = TRUE
#   # )
#   # ate(event = m.event,
#   #     treatment = m.treatment,
#   #     censor = m.censor,
#   #     data = dd, times = tau,
#   #     cause = 1)
#   map_X1_to_T1 <- function(dt){
#     dt$A_0 <- 1
#     dt
#   }
#   setnames(df, c("time_1", "event_1"), c("time", "event"))
#   if (conservative){
#     df[, cens_mg := 0]
#   } else {
#   mg <- influence_curve_censoring_martingale_test(
#     df,
#     m_event = m.event,
#     m_censor = m.censor,
#     treatment = 1,
#     tau = tau
#   )
#   df <- merge(df, mg, by = "id", all.x = TRUE)
#
#   df[is.na(cens_mg), c("cens_mg", "Q") := 0]
#   setkey(df, "time")
#   }
#   df[, propensity_score := predict(m.treatment, type = "response")]
#   df[, censoring_survival_predict := predict(m.censor, type = "survival")]
#   df[, F1tau := predictRisk(m.event,
#                             newdata = map_X1_to_T1(.SD),
#                             times = tau,
#                             cause = 1)]
#   browser()
#   df[, ic := 1 * (A_0 == 1) / propensity_score * ((1 * (time <= tau &
#                                                           event == 1) / censoring_survival_predict) - F1tau + cens_mg)]
#   df[, ic_cons := 1 * (A_0 == 1) / propensity_score * ((1 * (time <= tau &
#                                                                event == 1) / censoring_survival_predict) - F1tau)]
#   df[, ic := ic + F1tau - mean(F1tau)]
#   df[, ic_cons := ic_cons + F1tau - mean(F1tau)]
#   df[, .(
#     estimate = mean(F1tau) + mean(ic),
#     se = sd(ic) / sqrt(.N),
#     lower = mean(F1tau) + mean(ic) - 1.96 * sd(ic) / sqrt(.N),
#     upper = mean(F1tau) + mean(ic) + 1.96 * sd(ic) / sqrt(.N),
#     # estimate_cons = mean(F1tau) + mean(ic_cons),
#     # se_cons = sd(ic_cons) / sqrt(.N),
#     # lower_ci_cons = mean(F1tau) + mean(ic_cons) - 1.96 * sd(ic_cons) / sqrt(.N),
#     # upper_ci_cons = mean(F1tau) + mean(ic_cons) + 1.96 * sd(ic_cons) / sqrt(.N),
#     g_formula_estimate = mean(F1tau)
#   )]
# }

test_me <- function(d, tau, conservative = FALSE,return_df = FALSE) {
  influence_curve_censoring_martingale_test <- function(dt,
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
    my_covariate_dt <- my_covariate_dt[A_0 == 1]
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
    dt_Q_last <- my_dt[, .(Q_last = Q[.N]), by = id]
    cens_dt <- dt[time <= tau & event == 0, "time"]
    cens_dt_original <- copy(cens_dt)
    ## Cartesian product of cens_dt and my_covariate_dt

    cens_dt <- my_covariate_dt[, as.list(cens_dt), by = my_covariate_dt]

    ## rolling join (forward) to get Q at censoring times
    my_dt <- my_dt[cens_dt, roll = TRUE, on = c(name_covariates, "time")]
    my_dt <- merge(my_dt, dt_Q_last, by = "id")
    my_dt[is.na(Q), Q := 0]

    ## predict cumulative hazard function
    my_dt <- cumulative_hazard_cox(m_censor, my_dt, my_covariate_dt, cens_dt_original, 0)
    my_dt <- my_dt[, diff_Lambda_cause_0 := diff(c(0, Lambda_cause_0)), by = id]
    my_dt <- cumulative_hazard_cox(m_event$models[[1]], my_dt, my_covariate_dt, cens_dt_original, 1)
    my_dt <- cumulative_hazard_cox(m_event$models[[2]], my_dt, my_covariate_dt, cens_dt_original, 2)
    my_dt <- my_dt[, Scu := exp(-Lambda_cause_0)]
    my_dt <- my_dt[, Su :=  exp(-(Lambda_cause_1 + Lambda_cause_2))]

    ## define Q_last as the last Q within each id
    my_dt <- merge(my_dt, times_to_use, by = "id")
    no_id_match  <- my_dt[, (sum(time <= time_id) == 0), by = "id"][V1 == TRUE, ]$id
    res2 <- my_dt[id %in% no_id_match, .(cens_mg = 0, Q = Q_last[.N]), by = id]
    my_dt <- my_dt[time <= time_id]

    res <- my_dt[, .(cens_mg =
                       1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau & event_id[.N] == 0) - sum(1 / (Scu * Su) * (Q_last - Q) * diff_Lambda_cause_0),
                     Q = Q_last[.N]), by = id]
    rbind(res, res2)
  }

  df <- widen_continuous_data(d)$d_wide
  df <- df[order(df$time_1), ]

  levels(df$event_1) <- c(3,4,0,1,2)
  df$event_1 <- as.numeric(as.character(df$event_1))

  m.event <-  CSC(Hist(time_1, event_1) ~ A_0+L_0, data = df)
  m.censor <-  coxph(
    Surv(time_1, event_1 == 0) ~ A_0+L_0,
    data = df,
    x = TRUE,
    y = TRUE
  )
  m.treatment <-  glm(A_0 ~ L_0,
                      data = df,
                      family = binomial(link = "logit"))
  map_X1_to_T1 <- function(dt){
    dt$A_0 <- 1
    dt
  }
  setnames(df, c("time_1", "event_1"), c("time", "event"))
  if (conservative){
    df[, cens_mg := 0]
  } else {
    mg <- influence_curve_censoring_martingale_test(
      df,
      m_event = m.event,
      m_censor = m.censor,
      treatment = 1,
      tau = tau
    )
    df <- merge(df, mg, by = "id", all.x = TRUE)
    df[is.na(cens_mg), c("cens_mg", "Q") := 0]
    setkey(df, "time")
  }
  df[, propensity_score := predict(m.treatment, type = "response")]
  df[, censoring_survival_predict := predict(m.censor, type = "survival")]
  df[, F1tau := predictRisk(m.event,
                            newdata = map_X1_to_T1(.SD),
                            times = tau,
                            cause = 1,
                            product.limit=FALSE)] ##HSOULD BE FALSE
  # if (!all.equal(df[A_0==1]$Q,df[A_0==1]$F1tau)){
  #   browser()
  # }
  if (conservative){
    df[,Q:= F1tau]
  }
  df[, ic_init := 1 * (A_0 == 1) / propensity_score * ((1 * (time <= tau &
                                                          event == 1) / censoring_survival_predict) - Q + cens_mg)] ##HERE!The stupid difference is here; cannot put in Q, why???????
  df[, ic_cons_init := 1 * (A_0 == 1) / propensity_score * ((1 * (time <= tau &
                                                               event == 1) / censoring_survival_predict) - Q)]
  df[, ic := ic_init + F1tau - mean(F1tau)]
  df[, ic_cons := ic_cons_init + F1tau - mean(F1tau)]
  res <- df[, .(
    estimate = mean(F1tau) + mean(ic),
    se = sd(ic) / sqrt(.N),
    lower = mean(F1tau) + mean(ic) - 1.96 * sd(ic) / sqrt(.N),
    upper = mean(F1tau) + mean(ic) + 1.96 * sd(ic) / sqrt(.N),
    estimate_cons = mean(F1tau) + mean(ic_cons),
    se_cons = sd(ic_cons) / sqrt(.N),
    lower_ci_cons = mean(F1tau) + mean(ic_cons) - 1.96 * sd(ic_cons) / sqrt(.N),
    upper_ci_cons = mean(F1tau) + mean(ic_cons) + 1.96 * sd(ic_cons) / sqrt(.N),
    g_formula_estimate = mean(F1tau)
  )]
  if (return_df){
    list(res, df)
  } else {
    res
  }
}

