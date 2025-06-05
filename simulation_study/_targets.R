library(targets)
library(tarchetypes)
setwd("~/phd/continuous_time_LTMLE/simulation_study")
tar_option_set(
  packages = c("tarchetypes",
               "data.table",
               "riskRegression",
               "ranger",
               "survival",
               "ggplot2")
)
tar_source("functions")
time_covariates <- c("A", "L1", "L2")
baseline_covariates <- c("sex", "age", "A_0", "L_01", "L_02")
tau <- 0.04 ## time horizon

list(
  tar_target(true_value_three_event, {
    d_int <- simulate_continuous_time_data(n = 1000000, static_intervention = 1, number_events=3)
    calculate_mean(d_int, tau)
  }),
  tar_rep(debias_ipcw_tweedie, 
          command = simulate_and_run(
            n = 1000,
            number_events = 3,
            function_name = debias_ice_ipcw,
            function_args = list(
              tau = tau,
              model_type = "tweedie",
              time_covariates = time_covariates,
              baseline_covariates = baseline_covariates
            )
          ),           
          reps = 100,
          batch = 10
  ),
  tar_target(boxplot_debias_ipcw_tweedie, fun_boxplot(debias_ipcw_tweedie, true_value_three_event))
)
