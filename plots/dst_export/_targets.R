### _targets.R ---
#----------------------------------------------------------------------
## author:
## created: aug 15 2025 (11:38)
## Version:
## last-updated: sep  2 2025 (14:59) 
##     Update #: 478
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:
setwd("Z:/Workdata/703740/johanohlendorff/SGLT2")

# Load packages required to define the pipeline: ----
library(targets)
library(tarchetypes)
library(crew)
library(constructive)

## Source packages
tar_option_set(
  packages = c(
    "data.table", "ggplot2", "prodlim",
    "lubridate", "survival", "rtmle", "riskRegression", "constructive"
  ),
  format = "rds" # default storage format
  , 
  controller = crew_controller_local(
     workers = 16
  )
)

## Source funtions
tar_source("functions")
tar_source("conttimefunctions")

treat_names <- c("sglt2", "dpp4")
seed <- 9
model_pseudo_outcome <- "scaled_quasibinomial"
model_treatment <- "learn_glm_logistic" # learn_glm_logistic_special also possible
model_hazard <- "learn_coxph"
event_cutoff <- 20
k_lag <- 3
time_horizons <- 183 * (1:7) # 183 days = 6 months
B <- 30
eta <- 0.8

analyses_empa <- ## Run analyses
  tar_map(
    list(tau = time_horizons),
    tar_target(analysis_dpp4_empa, run_analysis(data_f,
      tau = tau,
      model_pseudo_outcome = model_pseudo_outcome,
      model_treatment = model_treatment,
      model_hazard = model_hazard,
      event_cutoff = event_cutoff,
      k_lag = k_lag,
      reg_analysis = "dpp4",
      treat_names = treat_names,
      seed = seed,
      B = B,
      eta = eta,
      baseline_covariates =  c("sex", "edu", "agegroup", "incomegroup", "diabetes_duration_group")
    )),
    tar_target(analysis_sglt2_empa, run_analysis(data_f,
      tau = tau,
      model_pseudo_outcome = model_pseudo_outcome,
      model_treatment = model_treatment,
      model_hazard = model_hazard,
      event_cutoff = event_cutoff,
      k_lag = k_lag,
      reg_analysis = "sglt2",
      treat_names = treat_names,
      seed = seed,
      B = B,
      eta = eta,
      baseline_covariates =  c("sex", "edu", "agegroup", "incomegroup", "diabetes_duration_group")
    )),
    tar_target(ate_empa, get_summary(analysis_sglt2_empa, analysis_dpp4_empa, n_empa, B, eta, tau)),
    tar_target(ate_empa_risk_difference, ate_empa$risk_difference),
    tar_target(ate_empa_risk, ate_empa$risk)
  )


analyses_empa_cat_hba1c <- ## Run analyses
  tar_map(
    list(tau = time_horizons),
    tar_target(analysis_dpp4_empa_cat_hba1c, run_analysis(data_f_cat_hba1c,
      tau = tau,
      model_pseudo_outcome = model_pseudo_outcome,
      model_treatment = model_treatment,
      model_hazard = model_hazard,
      event_cutoff = event_cutoff,
      k_lag = k_lag,
      reg_analysis = "dpp4",
      treat_names = treat_names,
      seed = seed,
      B = B,
      eta = eta,
      baseline_covariates =  c("sex", "edu", "agegroup", "incomegroup", "diabetes_duration_group")
    )),
    tar_target(analysis_sglt2_empa_cat_hba1c, run_analysis(data_f_cat_hba1c,
      tau = tau,
      model_pseudo_outcome = model_pseudo_outcome,
      model_treatment = model_treatment,
      model_hazard = model_hazard,
      event_cutoff = event_cutoff,
      k_lag = k_lag,
      reg_analysis = "sglt2",
      treat_names = treat_names,
      seed = seed,
      B = B,
      eta = eta,
      baseline_covariates =  c("sex", "edu", "agegroup", "incomegroup", "diabetes_duration_group")
    )),
    tar_target(ate_empa_cat_hba1c, get_summary(analysis_sglt2_empa_cat_hba1c, analysis_dpp4_empa_cat_hba1c, n_empa, B, eta, tau)),
    tar_target(ate_empa_cat_hba1c_risk_difference, ate_empa_cat_hba1c$risk_difference),
    tar_target(ate_empa_cat_hba1c_risk, ate_empa_cat_hba1c$risk)
  )

list(
  ## Load objects from Puriyas project
  tar_target(dt_sgl_dpp4, readRDS("objects/dt_sgl_dpp4")), ## Treatment
  tar_target(dt_lab, readRDS("objects/dt_lab")), ## Lab measurements, i.e., HbA1c
  ## tar_target(dt_outcomes, readRDS("objects/dt_outcomes")), ## Outcomes;
  tar_target(death, readRDS("objects/death")), ## Death
  tar_target(immiemi, readRDS("objects/immiemi")), ## Emmigration
  # Applying EMPA-REG exclusions
  tar_target(baseline_full, readRDS("objects/dt_baseline_allvar_LTMLEprep")),
  
  ## Format variables
  tar_target(regime_and_ids, get_regime(dt_sgl_dpp4[pnr %in% baseline_full$pnr], dt_lab[pnr %in% baseline_full$pnr])), ## A_0: 1 if you bought corresponding medicine. A keeps being 1 until you buy the other medicine. Visitation times = purchase times of both medicines
  tar_target(outcome, get_outcome(death[pnr %in% baseline_full$pnr], immiemi[pnr %in% baseline_full$pnr], regime_and_ids$dt_index, regime_and_ids$ids_hba1c_measured)), ## Deatj
  tar_target(valid_ids, regime_and_ids$ids_hba1c_measured),
  tar_target(regime, regime_and_ids$regime[pnr %in% valid_ids]),
  tar_target(dt_index, regime_and_ids$dt_index[pnr %in% valid_ids]),
  tar_target(hba1c, get_hba1c(dt_lab[pnr %in% valid_ids], dt_index)),
  tar_target(baseline, baseline_full[, c("pnr", "sex", "edu", "agegroup", "incomegroup", "diabetes_duration_group"), with=FALSE]),
  tar_target(n_empa, length(valid_ids)), ## same number as Puriyas LTMLE analysis
  ## Format to expected continuous time longitudinal format for the `debias_ice_ipcw` function.
  tar_target(data_f, clean_and_combine(
    list(regime, hba1c), outcome, baseline,
    treat_names, "hba1c", FALSE
  )),
  analyses_empa,
  tar_combine(
    ate_empa_risk_difference,
    analyses_empa[["ate_empa_risk_difference"]],
    command = dplyr::bind_rows(!!!.x)
  ),
  tar_combine(
    ate_empa_risk,
    analyses_empa[["ate_empa_risk"]],
    command = dplyr::bind_rows(!!!.x)
  ),
  tar_target(plot_empa, {
    p1 <- ggplot(ate_empa_risk_difference, aes(x = time_horizon, y = estimate, color = ci_method)) +
      geom_line() +
      geom_ribbon(aes(ymin = lower, ymax = upper, color = ci_method), alpha = 0.3) +
      theme_bw() +
      facet_grid(~estimator) +
      xlab("Time (days)") +
      ylab("Risk difference of death (SGLT2 vs DPP4)") +
      labs(color = "CI method") +
      scale_y_continuous(labels = scales::percent)
    p2 <- ggplot(ate_empa_risk, aes(x = time_horizon, y = estimate, linetype = ci_method, color = Treatment)) +
      geom_line() +
      geom_ribbon(aes(ymin = lower, ymax = upper, linetype = ci_method, color = Treatment), alpha = 0.3) +
      theme_bw() +
      facet_grid(~estimator) +
      xlab("Time (days)") +
      ylab("Risk of death") +
      labs(color = "Treatment", linetype = "CI method") +
      scale_y_continuous(labels = scales::percent)
    list(p1, p2)
  }),
  tar_target(data_f_cat_hba1c, clean_and_combine(
    list(regime, hba1c), outcome, baseline,
    treat_names, "hba1c", TRUE
  )),
  analyses_empa_cat_hba1c,
  tar_combine(
    ate_empa_cat_hba1c_risk_difference,
    analyses_empa_cat_hba1c[["ate_empa_cat_hba1c_risk_difference"]],
    command = dplyr::bind_rows(!!!.x)
  ),
  tar_combine(
    ate_empa_cat_hba1c_risk,
    analyses_empa_cat_hba1c[["ate_empa_cat_hba1c_risk"]],
    command = dplyr::bind_rows(!!!.x)
  ),
  tar_target(plot_empa_cat_hba1c, {
    p1 <- ggplot(ate_empa_cat_hba1c_risk_difference[!(estimator == "ICE-IPCW (Debiased)" & ci_method == "Cheap Subsampling \n (m = 12750, B = 30)")], aes(x = time_horizon, y = estimate, color = ci_method)) +
      geom_line() +
      geom_ribbon(aes(ymin = lower, ymax = upper, color = ci_method), alpha = 0.3) +
      theme_bw() +
      facet_grid(~estimator) +
      xlab("Time (days)") +
      ylab("Risk difference of death (SGLT2 vs DPP4)") +
      labs(color = "CI method") +
      scale_y_continuous(labels = scales::percent)
    p2 <- ggplot(ate_empa_cat_hba1c_risk[!(estimator == "ICE-IPCW (Debiased)" & ci_method == "Cheap Subsampling \n (m = 12750, B = 30)")], aes(x = time_horizon, y = estimate, linetype = ci_method, color = Treatment)) +
      geom_line() +
      geom_ribbon(aes(ymin = lower, ymax = upper, linetype = ci_method, color = Treatment), alpha = 0.3) +
      theme_bw() +
      facet_grid(~estimator) +
      xlab("Time (days)") +
      ylab("Risk of death") +
      labs(color = "Treatment", linetype = "CI method") +
      scale_y_continuous(labels = scales::percent)
    list(p1, p2)
  })
)
#----------------------------------------------------------------------
### _targets.R ends here
