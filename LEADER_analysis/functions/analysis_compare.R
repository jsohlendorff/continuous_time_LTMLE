analysis_compare <- function(data,
                             grid_size,
                             tau,
                             model_pseudo_outcome = "quasibinomial",
                             model_treatment = "learn_glm_logistic",
                             timevarying_vars,
                             baseline_vars,
                             event_cutoff,
                             k_lag = 3,
                             verbose = FALSE,
                             learner_rtmle = "learn_glmnet") {
  data$timevarying_data$id <- as.numeric(data$timevarying_data$id)
  data$baseline_data$id <- as.numeric(data$baseline_data$id)
  res <- debias_ice_ipcw(
    data = data,
    tau = tau,
    model_pseudo_outcome = model_pseudo_outcome,
    model_treatment = model_treatment,
    model_hazard = NULL,
    time_covariates = c("A", timevarying_vars),
    baseline_covariates = c("A_0", baseline_vars),
    last_event_number = event_cutoff,
    conservative = TRUE,
    k_lag = 3, ## Only use three last events in nuisance parameter estimation
    verbose = verbose
  )
  res_ltmle <- apply_rtmle(data,
    tau = tau,
    grid_size = grid_size,
    time_confounders = timevarying_vars,
    time_confounders_baseline = paste(timevarying_vars, "0", sep = "_"),
    baseline_confounders = baseline_vars,
    learner = learner_rtmle
  )
  itt <- list(estimate = data$timevarying_data[event %in% c("C", "Y", "D"), mean(time <= tau & event == "Y")])
  list(
    res = res,
    itt = itt,
    res_ltmle = res_ltmle
  )
}

get_risk_difference <- function(res_lira, res_placebo) {
  risk_diff <- res_lira$res$estimate - res_placebo$res$estimate
  risk_diff_ltmle <- res_lira$res_ltmle$estimate - res_placebo$res_ltmle$estimate
  se <- sqrt(
    res_lira$res$se^2 + res_placebo$res$se^2
  )
  se_ltmle <- sqrt(
    res_lira$res_ltmle$se^2 + res_placebo$res_ltmle$se^2
  )
  list(
    debias_ice = data.frame(
      risk_difference = risk_diff,
      se = se,
      ci_lower = risk_diff - 1.96 * se,
      ci_upper = risk_diff + 1.96 * se,
      p_value = 2 * pnorm(-abs(risk_diff / se))
    ),
    ltmle = data.frame(
      risk_difference = risk_diff_ltmle,
      se = se_ltmle,
      ci_lower = risk_diff_ltmle - 1.96 * se_ltmle,
      ci_upper = risk_diff_ltmle + 1.96 * se_ltmle,
      p_value = 2 * pnorm(-abs(risk_diff_ltmle / se_ltmle))
    )
  )
}
