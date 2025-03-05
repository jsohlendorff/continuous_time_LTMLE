library(targets)
library(tarchetypes)
setwd("~/phd/continuous_time_LTMLE/")
tar_option_set(
  packages = c("tarchetypes", "data.table", "riskRegression", "ranger", "survival","ggplot2")
)
tar_source("continuous_time_functions.R")
tau <- 0.02

fun_boxplot = function(d,true_value){
  d <- data.frame(estimate=d)
  ggplot2::ggplot(data = d, aes(y = estimate)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(yintercept = true_value, color = "red")
}

list(
  # tar_target(true_value_one_event, {
  #   d_int <- simulate_continuous_time_data(n = 1000000, static_intervention = 1, number_events=1)
  #   calculate_mean(d_int, tau, number_events=1)
  # }),
  tar_target(true_value_two_event, {
    d_int <- simulate_continuous_time_data(n = 1000000, static_intervention = 1, number_events=2)
    calculate_mean(d_int, tau, number_events=2)
  }),
  tar_target(true_value_three_event, {
    d_int <- simulate_continuous_time_data(n = 1000000, static_intervention = 1, number_events=3)
    calculate_mean(d_int, tau, number_events=3)
  }),
  tar_target(true_value_five_events, {
    d_int <- simulate_continuous_time_data(n = 1000000, static_intervention = 1, number_events=3)
    calculate_mean(d_int, tau, number_events=5)
  }),

  # tar_rep(method3_one_event, ## works well even if we can't correctly specify the regression
  #         command = {
            # d <- simulate_continuous_time_data(n = 10000, number_events=1)
            # test_fun_method_3(d, tau = tau, model_type = "glm")
  #         },
  #         reps = 100,
  #         batch = 10
  # ),
  # tar_rep(method2_sim_one_event, ## biased; need to find out why
  #         command = {
            # d <- simulate_continuous_time_data(n = 5000, number_events=1)
            # test_fun_method_2(d, tau = tau, model_type = "glm")
  #         },
  #         reps = 10,
  #         batch = 100
  # ),
  # tar_rep(method3_two_event_uncensored, ## works well even if we can't correctly specify the regression
  #         command = {
  #           d <- simulate_continuous_time_data(n = 2000, number_events=2, uncensored=TRUE)
  #           test_fun_method_3(d, tau = tau, model_type = "glm")
  #         },
  #         reps = 100,
  #         batch = 10
  # ),
  tar_rep(method3_two_event_scaled_quasi, ## works well even if we can't correctly specify the regression
          command = {
            d <- simulate_continuous_time_data(n = 2000, number_events=2)
            test_fun_method_3(d, tau = tau, model_type = "glm", model_type_cens = "scaled_quasibinomial")
          },
          reps = 300,
          batch = 10
  ),
  tar_rep(method3_three_event_scaled_quasi, ## works well even if we can't correctly specify the regression
          command = {
            d <- simulate_continuous_time_data(n = 2000, number_events=3)
            test_fun_method_3(d, tau = tau, model_type = "glm", model_type_cens = "scaled_quasibinomial")
          },
          reps = 100,
          batch = 30
  ),
  tar_rep(method3_five_event_scaled_quasi, ## works well even if we can't correctly specify the regression
          command = {
            d <- simulate_continuous_time_data(n = 2000, number_events=5)
            test_fun_method_3(d, tau = tau, model_type = "glm", model_type_cens = "scaled_quasibinomial")
          },
          reps = 100,
          batch = 30
  ),
  # tar_rep(method3_two_event_tweedie,
  #         command = {
  #           d <- simulate_continuous_time_data(n = 2000, number_events=2)
  #           test_fun_method_3(d, tau = tau, model_type = "glm",  model_type_cens = "tweedie")
  #         },
  #         reps = 100,
  #         batch = 10
  # ),
  tar_rep(method3_two_event_gamma_mixture,
          command = {
            d <- simulate_continuous_time_data(n = 2000, number_events=2)
            test_fun_method_3(d, tau = tau, model_type = "glm", model_type_cens = "gamma_mixture")
          },
          reps = 100,
          batch = 10
  ),
  tar_rep(ipw_two_event, ## works well even if we can't correctly specify the regression
          command = {
            d <- simulate_continuous_time_data(n = 2000, number_events=2)
            test_fun_method_ipw(d, tau = tau, model_type = "glm")
          },
          reps = 100,
          batch = 10
  ),

  # tar_rep(method2_two_event, ## biased; need to find out why
  #         command = {
  #           d <- simulate_continuous_time_data(n = 2500, number_events=2)
  #           test_fun_method_2(d, tau = tau, model_type = "glm")
  #         },
  #         reps = 10,
  #         batch = 100
  # ),
  ## make boxplots
  # tar_target(boxplot_method_3_one_event, fun_boxplot(method3_one_event, true_value_one_event)),
  # tar_target(boxplot_method_2_one_event, fun_boxplot(method2_sim_one_event, true_value_one_event)),
  tar_target(boxplot_method_3_two_event_scaled_quasi, fun_boxplot(method3_two_event_scaled_quasi, true_value_two_event)),
  # tar_target(boxplot_method_3_two_event_tweedie, fun_boxplot(method3_two_event_tweedie, true_value_two_event)),
  tar_target(boxplot_method_3_two_event_gamma_mixture, fun_boxplot(method3_two_event_gamma_mixture, true_value_two_event)),
  tar_target(boxplot_method_3_five_event_scaled_quasi, fun_boxplot(method3_five_event_scaled_quasi, true_value_five_events)),
  tar_target(boxplot_ipw_two_event, fun_boxplot(ipw_two_event, true_value_two_event)),
  tar_target(boxplot_method_3_three_event_scaled_quasi, fun_boxplot(method3_three_event_scaled_quasi, true_value_three_event))
  # tar_target(boxplot_method_3_two_event_uncensored, fun_boxplot(method3_two_event_uncensored, true_value_two_event))
  # MAke boxplots comparing the three methods
  # tar_target(boxplot_method_2_two_event, fun_boxplot(method2_two_event, true_value_two_event))
  # tar_rep(method3_three_events,
  #   command = {
  #     d <- simulate_continuous_time_data(n = 10000, number_events=3)
  #     test_fun_method_3(d, tau = tau, model_type = "glm")
  #   },
  #   reps = 100,
  #   batch = 10
  # ),
  # tar_rep(method2_sim_three_events,
  #         command = {
  #           d <- simulate_continuous_time_data(n = 10000, number_events=3)
  #           test_fun_method_2(nd, tau = tau, model_type = "glm")
  #         },
  #         reps = 10,
  #         batch = 100
  # )
)
