library(targets)
library(tarchetypes)
library(crew)
setwd("~/phd/continuous_time_LTMLE/simulation_study")
tar_option_set(
    packages = c("tarchetypes",
                 "data.table",
                 "riskRegression",
                 "ranger",
                 "survival",
                 "ggplot2",
                 "rtmle"),
    controller = crew_controller_local(workers = 4)
)

tar_source("functions")
time_covariates <- c("A", "L1", "L2")
baseline_covariates <- c("sex", "age", "A_0", "L_01", "L_02")
tau <- 80 ## time horizon
values <-
    expand.grid(
        model_pseudo_outcome = c("tweedie", "scaled_quasibinomial"),
        conservative = c(TRUE, FALSE)
    )

list(
    tar_target(true_value_three_event, {
        d_int <- simulate_continuous_time_data(n = 2500000, static_intervention = 1, number_events=3)
        calculate_mean(d_int, tau)
    }),
    ## Apply debiased ICE-IPCW procedure + 
    tar_map_rep(
        name = debias_ipcw,
        command = simulate_and_run(
            n = 1000,
            number_events = 3,
            function_name = debias_ice_ipcw,
            function_args = list(
                tau = tau,
                model_pseudo_outcome = model_pseudo_outcome,
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = time_covariates,
                baseline_covariates = baseline_covariates,
                conservative = conservative
            )
        ),
        values = values,
        reps = 100,
        batch = 10
    ),
    ## Apply debiased ICE-IPCW procedure with uncensored data
    tar_rep(debias_ipcw_uncensored, simulate_and_run(n = 1000,
                                                      number_events = 3,
                                                      function_name = debias_ice_ipcw,
                                                      uncensored = TRUE,
                                                      function_args = list(
                                                          tau = tau,
                                                          model_pseudo_outcome = "quasibinomial",
                                                          model_treatment = "learn_glm_logistic",
                                                          model_hazard = NULL,
                                                          time_covariates = time_covariates,
                                                          baseline_covariates = baseline_covariates,
                                                          conservative = TRUE
                                                      )),
            reps = 100,
            batch = 10),
    
    ## LTMLE
    tar_rep(ltmle_grid_10, simulate_and_run(n = 1000,
                                            number_events = 3,
                                            function_name = apply_rtmle,
                                            function_args = list(
                                                tau = tau,
                                                grid_size = 10,
                                                time_confounders = setdiff(time_covariates, "A"),
                                                time_confounders_baseline = c("L_01", "L_02"),
                                                baseline_confounders = baseline_covariates,
                                                learner = "learn_glmnet"
                                            )),
            reps = 100,
            batch = 10),
    
    
    ## Boxplots for debiased IPCW estimates
    tar_target(boxplot_debias_ipcw, fun_boxplot(debias_ipcw, true_value_three_event, by = c("model_pseudo_outcome", "conservative"))),
    ## Boxplots for debiased IPCW estimates with uncensored data
    tar_target(boxplot_debias_ipcw_uncensored, fun_boxplot(debias_ipcw_uncensored, true_value_three_event)),
    
    ## Boxplots for LTMLE estimates
    tar_target(boxplot_ltmle_grid_10, fun_boxplot_rtmle(ltmle_grid_10, true_value_three_event))
)
