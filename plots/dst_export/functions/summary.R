### summary.R ---
#----------------------------------------------------------------------
## author:
## created: aug 20 2025 (14:16)
## Version:
## last-updated: sep  2 2025 (14:59) 
##     Update #: 64
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:
summary_fun <- function(ic, estimate, estimate_b, estimate_ice, estimate_b_ice, n_subset, B, eta, tau) {
  SE <- sd(ic) / (sqrt(n_subset))
  if (!is.null(B)) {
    subsample_size <- round(eta * n_subset)
    cb <- cheap_confidence_interval(estimate,
      estimate_b,
      subsample_size,
      n_subset,
      0.05,
      type = "subsampling"
    )[B, c("cheap_lower", "cheap_upper")]
    cb_ice <- cheap_confidence_interval(estimate_ice,
      estimate_b_ice,
      subsample_size,
      n_subset,
      0.05,
      type = "subsampling"
    )[B, c("cheap_lower", "cheap_upper")]
  }
  cat_cheap <- paste0("Cheap Subsampling \n (m = ", subsample_size, ", B = ", B, ")")
  data.table(
    estimate = c(estimate, estimate, estimate_ice),
    se = c(SE, NA, NA),
    lower = c(estimate - 1.96 * SE, cb$cheap_lower, cb_ice$cheap_lower),
    upper = c(estimate + 1.96 * SE, cb$cheap_upper, cb_ice$cheap_upper),
    ci_method = c("Influence Curve", cat_cheap, cat_cheap),
    estimator = c("ICE-IPCW (Debiased)", "ICE-IPCW (Debiased)", "ICE-IPCW"),
    time_horizon = tau
  )
}
get_summary <- function(analysis_sglt2, analysis_dpp4, n_subset, B, eta, tau) {
  #analysis_sglt2$res_B <- analysis_sglt2$res_B[estimate > 0 & estimate < 1]
  #analysis_dpp4$res_B <- analysis_dpp4$res_B[estimate > 0 & estimate < 1]
  #B <- nrow(analysis_dpp4$res_B)
  risk_difference <- summary_fun(
    analysis_sglt2$res$ic - analysis_dpp4$res$ic,
    analysis_sglt2$res$result$estimate - analysis_dpp4$res$result$estimate,
    analysis_sglt2$res_B$estimate - analysis_dpp4$res_B$estimate,
    analysis_sglt2$res$result$ice_ipcw_estimate - analysis_dpp4$res$result$ice_ipcw_estimate,
    analysis_sglt2$res_B$ice_ipcw_estimate - analysis_dpp4$res_B$ice_ipcw_estimate,
    n_subset,
    B,
    eta,
    tau
  )
  risk_sglt2 <- summary_fun(
    analysis_sglt2$res$ic,
    analysis_sglt2$res$result$estimate,
    analysis_sglt2$res_B$estimate,
    analysis_sglt2$res$result$ice_ipcw_estimate,
    analysis_sglt2$res_B$ice_ipcw_estimate,
    n_subset,
    B,
    eta,
    tau
  )
  risk_dpp4 <- summary_fun(
    analysis_dpp4$res$ic,
    analysis_dpp4$res$result$estimate,
    analysis_dpp4$res_B$estimate,
    analysis_dpp4$res$result$ice_ipcw_estimate,
    analysis_dpp4$res_B$ice_ipcw_estimate,
    n_subset,
    B,
    eta,
    tau
  )
  risk_sglt2$Treatment <- "SGLT2"
  risk_dpp4$Treatment <- "DPP4"
  risk <- rbind(risk_dpp4, risk_sglt2)
  return(list(risk_difference = risk_difference, risk = risk))
}

#----------------------------------------------------------------------
### summary.R ends here
