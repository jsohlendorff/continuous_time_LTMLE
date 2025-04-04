library(targets)
library(tarchetypes)
setwd("~/phd/continuous_time_LTMLE/")
tar_option_set(
  packages = c("tarchetypes", "data.table", "riskRegression", "ranger", "survival","ggplot2")
)
tar_source("continuous_time_functions.R")
tar_source("calculate_ic.R")
time_covariates <- c("A", "L")
baseline_covariates <- c("sex", "age", "A_0", "L_0")
tau <- 0.04

fun_boxplot = function(d,true_value){
  ## calculate coverage
  cov<-d[, .(coverage=mean((true_value > lower) & (true_value < upper)))]
  p<-ggplot2::ggplot(data = d, aes(y = estimate)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = true_value, color = "red")) +
    ggplot2::theme_minimal()
  q <- ggplot2::ggplot(data = d, aes(y = se)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = sd(estimate), color = "red")) +
    ggplot2::theme_minimal()
  list(p, q, cov)
}

simulate_and_run <- function(n, number_events, function_name, function_args){
  d <- simulate_continuous_time_data(n = n, number_events = number_events)
  do.call(function_name, c(list(d), function_args))
}

list(
  tar_target(true_value_three_event, {
    d_int <- simulate_continuous_time_data(n = 1000000, static_intervention = 1, number_events=3)
    calculate_mean(d_int, tau)
  }),
  tar_rep(debias_ipcw_scaled_quasi_three, 
          command = simulate_and_run(
            n = 1000,
            number_events = 3,
            function_name = debias_ipcw,
            function_args = list(
              tau = tau,
              model_type = "tweedie",
              time_covariates = time_covariates,
              baseline_covariates = baseline_covariates
            )
          ),           reps = 100,
          batch = 10
  ),
  tar_target(boxplot_debias_ipcw_scaled_quasi_three, fun_boxplot(debias_ipcw_scaled_quasi_three, true_value_three_event))
)
