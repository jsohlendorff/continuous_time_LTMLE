## Targets file for the LEADER analysis
## Possible strong points of dispute are denoted with `!!!`
## TODO: Move more of the data cleaning to single targets
## The target parameter is the absolute risk of MACE within 3 years
## Under the intervention that the doctor enforces treatment
## as part of the 11 first events.
library(targets)
library(data.table)

## Setup
try(setwd("~/phd/continuous_time_LTMLE/LEADER_analysis/"), silent = TRUE)
tar_option_set(
  format = "qs", # Use 'qs' for fast serialization
  packages = c("data.table", "lubridate", "tidyr", "survminer", "survival"), # Load necessary packages
  memory = "transient" # Use transient memory to avoid storing large objects permanently
)

if (dir.exists("~/projects/LEADER_analysis/_targets/objects/")) {
  leader_targets_directory <- "~/projects/LEADER_analysis/_targets/objects/"
}
tar_source("functions")
tar_source("../simulation_study/functions/") ## Continuous time functions

## Time horizon is selected such that (essentially) no censoring occurs in the data.
tau <- 3 * 360 # 3 years in days
last_event_number <- 11 # We assume that the doctor enforces treatment as part of the first 11 events/registrations

## Which variables to use in the analysis?
baseline_vars <- c(
  "sex",
  "age",
  "diabetesdurationgroup",
  "ethnic",
  "egfr.baseline",
  "hba1c.baseline",
  "heart.failure",
  "renal.cat"
)
timevarying_vars <- c(
  "heart_failures",
  "nausea_and_vomiting_symptoms",
  "atrial_fibrillation",
  "diarrhoea",
  "insulin",
  "thiazo",
  "metformin",
  "sulfonylurea",
  "alfa_g_inhib",
  "dpp4"
)

list(
  ## Load the data files from Kathrines RE-LEADER analysis
  tar_target(
    dt_baseline,
    readRDS(paste0(leader_targets_directory, "dt_baseline"))[, c("id", baseline_vars), with = FALSE]
  ),
  tar_target(
    dt_timevarying,
    readRDS(paste0(leader_targets_directory, "dt_timevarying"))
  ),
  tar_target(
    dt_outcome,
    readRDS(paste0(leader_targets_directory, "dt_outcome"))
  ),
  tar_target(
    dt_index,
    readRDS(paste0(leader_targets_directory, "dt_index"))
  ),
  tar_target(
    dt_regime,
    readRDS(paste0(leader_targets_directory, "dt_regime"))
  ),
  ## Ensure compatible column names between data
  tar_target(
    comedication,
    {
      comed <- dt_timevarying$conmed
      comed[, medcode := NULL] ## Not needed
      setnames(comed, c("start.treatment", "end.treatment"), c("start_date", "end_date"))
      comed
    }
  ),
  tar_target(
    adverse_events,
    {
      adverse <- dt_timevarying$adverse
      setnames(adverse, c("adverse.event", "ae.st.date", "ae.end.date"), c("X", "start_date", "end_date"))
      adverse
    }
  ),
  tar_target(
    regime,
    {
      dt_regime[, dose := NULL] # We do not dosages in the analysis into account
      setnames(dt_regime, c("treatment", "start_treatment", "end_treatment"), c("X", "start_date", "end_date"))
      dt_regime
    }
  ),
  ## Get the ids of the patients in each treatment group
  tar_target(
    id_regimen_lira,
    dt_index[randomization_group == "Lira", id],
  ),
  tar_target(
    id_regimen_placebo,
    dt_index[randomization_group == "Placebo", id],
  ),
  ## Clean the data
  ## !!! We only care about the times of medications if they are stopped or started for longer periods of time !!!
  ## Here you are not counted as being off the medication if you stop it for less than 14 days.
  ## See `remove_superfluous_info` function for details
  tar_target(
    comedication_cleaned,
    {
      r <- clean(comedication, dt_index, period = 14, type = "comedication")
      r[X != "insulin_one", ]
    }
  ),
  tar_target(
    adverse_events_cleaned,
    clean(adverse_events, dt_index, period = 1, type = "event")
  ),
  tar_target(
    regime_cleaned,
    clean(regime, dt_index, period = 14, type = "primary_treatment")
  ),
  tar_target(
    outcome_cleaned,
    clean_outcome(dt_outcome, dt_index,
      event_of_interest = "primary.outcome"
    ) # MACE is the event of interest
  ),
  ## Combine cleaned into a single data.table in the long format for continuous-time debias ICE-IPCW estimation
  tar_target(
    combined_data_lira,
    combine(
      comedication_cleaned,
      adverse_events_cleaned,
      regime_cleaned,
      outcome_cleaned,
      outcomes = c("all_cause_mortality", "mace", "censored"),
      treat_name = "lira",
      id_regimen = id_regimen_lira
    )
  ),
  tar_target(
    combined_data_placebo,
    combine(
      comedication_cleaned,
      adverse_events_cleaned,
      regime_cleaned,
      outcome_cleaned,
      outcomes = c("all_cause_mortality", "mace", "censored"),
      treat_name = "placebo",
      id_regimen = id_regimen_placebo
    )
  ),
  ## Summarize the data
  ## How many are at risk of a terminal event before tau after "event_number" events?
  ## !!! We cannot reliably enforce the intervention if there aren't enough people at risk !!!
  tar_target(
    at_risk_lira,
    at_risk(combined_data_lira, tau)
  ),
  tar_target(
    at_risk_placebo,
    at_risk(combined_data_placebo, tau)
  ),
  ## Censored plots; deviation from protocol + censoring
  tar_target(
    plot_censored_lira,
    censored_plot(combined_data_lira, "lira", tau, outcomes = c("all_cause_mortality", "mace", "censored"))
  ),
  tar_target(
    plot_censored_placebo,
    censored_plot(combined_data_placebo, "placebo", tau, outcomes = c("all_cause_mortality", "mace", "censored"))
  ),
  ## Make data into format for the continuous_time debiased ICE-IPCW estimation
  ## !!! We make every non-terminal event a treatment event, so that we assume that the doctor makes treatment decisions at each event time !!!
  ## Based on at_risk_lira and at_risk_placebo, we pick the first 10 events for each patient
  ## TODO; The fact that the treatment variable has to be called "A" should be changed in the future.
  tar_target(
    data_lira,
    format_data(
      combined_data_lira,
      dt_baseline,
      outcomes = c("all_cause_mortality", "mace", "censored"),
      treat_name = "lira",
      event_cutoff = last_event_number,
      every_event_visitation_time = TRUE,
      tau = tau
    )
  ),
  tar_target(
    data_placebo,
    format_data(
      combined_data_placebo,
      dt_baseline,
      outcomes = c("all_cause_mortality", "mace", "censored"),
      treat_name = "placebo",
      event_cutoff = last_event_number,
      every_event_visitation_time = TRUE,
      tau = tau
    )
  ),
  ## Run debiased procedure on Liraglutide
  tar_target(
    res_lira,
    {
      res <- debias_ice_ipcw(
        data = data_lira,
        tau = tau,
        model_pseudo_outcome = "quasibinomial",
        model_treatment = "learn_glm_logistic",
        model_hazard = NULL,
        time_covariates = c("A", timevarying_vars),
        baseline_covariates = c("A_0", baseline_vars),
        last_event_number = last_event_number,
        conservative = TRUE
      )
      itt <- list(estimate = data_lira$timevarying_data[event %in% c("C", "Y", "D"), mean(time <= tau & event == "Y")])
      list(
        res = res,
        itt = itt
      )
    }
  ),
  ## Run debiased procedure on Placebo
  tar_target(
    res_placebo,
    {
      res <- debias_ice_ipcw(
        data = data_placebo,
        tau = tau,
        model_pseudo_outcome = "quasibinomial",
        model_treatment = "learn_glm_logistic",
        model_hazard = NULL,
        time_covariates = c("A", timevarying_vars),
        baseline_covariates = c("A_0", baseline_vars),
        last_event_number = last_event_number,
        conservative = TRUE
      )
      itt <- list(estimate = data_placebo$timevarying_data[event %in% c("C", "Y", "D"), mean(time <= tau & event == "Y")])
      list(
        res = res,
        itt = itt
      )
    }
  ),
  ## The procedure seems uncertain about placebo. The `ipw` and `ice_ipcw_estimate` estimates are close for Liraglutide but not Placebo?
  tar_target(
    risk_difference,
    {
      risk_diff <- res_lira$res$estimate - res_placebo$res$estimate
      se <- sqrt(
        res_lira$res$se^2 + res_placebo$res$se^2
      )
      list(
        risk_difference = risk_diff,
        se = se,
        ci_lower = risk_diff - 1.96 * se,
        ci_upper = risk_diff + 1.96 * se
      )
    }
  ),
  ## Sensitivity analysis with every event visitation time = FALSE
  tar_target(
    data_lira_sensitivity,
    format_data(
      combined_data_lira,
      dt_baseline,
      outcomes = c("all_cause_mortality", "mace", "censored"),
      treat_name = "lira",
      event_cutoff = last_event_number,
      every_event_visitation_time = FALSE,
      tau = tau
    )
  ),
  tar_target(
    data_placebo_sensitivity,
    format_data(
      combined_data_placebo,
      dt_baseline,
      outcomes = c("all_cause_mortality", "mace", "censored"),
      treat_name = "placebo",
      event_cutoff = last_event_number,
      every_event_visitation_time = FALSE,
      tau = tau
    )
  )
  ## FIXME: Does not work.
  # tar_target(
  #   res_lira_sensitivity,
  #   {
  #     res <- debias_ice_ipcw(
  #       data = data_lira_sensitivity,
  #       tau = tau,
  #       model_pseudo_outcome = "quasibinomial",
  #       model_treatment = "learn_glm_logistic",
  #       model_hazard = NULL,
  #       time_covariates = c("A", timevarying_vars),
  #       baseline_covariates = c("A_0", baseline_vars),
  #       last_event_number = last_event_number,
  #       conservative = TRUE
  #     )
  #     itt <- list(estimate = data_lira_sensitivity$timevarying_data[event %in% c("C", "Y", "D"), mean(time <= tau & event == "Y")])
  #     list(
  #       res = res,
  #       itt = itt
  #     )
  #   }
  # ),
  # tar_target(
  #   res_placebo_sensitivity,
  #   {
  #     res <- debias_ice_ipcw(
  #       data = data_placebo_sensitivity,
  #       tau = tau,
  #       model_pseudo_outcome = "quasibinomial",
  #       model_treatment = "learn_glm_logistic",
  #       model_hazard = NULL,
  #       time_covariates = c("A", timevarying_vars),
  #       baseline_covariates = c("A_0", baseline_vars),
  #       last_event_number = last_event_number,
  #       conservative = TRUE
  #     )
  #     itt <- list(estimate = data_placebo_sensitivity$timevarying_data[event %in% c("C", "Y", "D"), mean(time <= tau & event == "Y")])
  #     list(
  #       res = res,
  #       itt = itt
  #     )
  #   }
  # ),
  # tar_target(
  #   risk_difference_sensitivity,
  #   {
  #     risk_diff <- res_lira_sensitivity$res$estimate - res_placebo_sensitivity$res$estimate
  #     se <- sqrt(
  #       res_lira_sensitivity$res$se^2 + res_placebo_sensitivity$res$se^2
  #     )
  #     list(
  #       risk_difference = risk_diff,
  #       se = se,
  #       ci_lower = risk_diff - 1.96 * se,
  #       ci_upper = risk_diff + 1.96 * se
  #     )
  #   }
  # )
)
