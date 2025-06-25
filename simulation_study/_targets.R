## Simulation study for the continuous-time ICE-IPCW estimator
## and its debiased version, estimating the average treatment effect
## of the mean interventional absolute risk for the "as-treated" intervention.
## Focus on three events in total (K = 3).
## Compare with LTMLE (Longitudinal Targeted Maximum Likelihood Estimation)
## Check functions/simulate.R for details about the simulation mechanism.
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
                 "rtmle",
                 "survminer"),
    controller = crew_controller_local(workers = 8)
)

tar_source("functions")
time_covariates <- c("A", "L")
baseline_covariates <- c("age", "A_0", "L_0")

## Here, we vary the effects of the treatment A and the time-varying confounder L
## has on the outcome via A on Y, L on Y, and L on A. The last three cases correspond to no confounding effect.
values <- data.frame(
    effect_A_on_Y = c(-0.15, 0, 0.15, -0.15, -0.15, -0.15, -0.15, -0.15, 0, 0.15),
    effect_L_on_Y = c(0.25, 0.25, 0.25, -0.25, 0, 0.25, 0.25, 0, 0, 0),
    effect_L_on_A = c(-0.1, -0.1, -0.1, -0.1, -0.1,0, 0.1, 0, 0, 0)
)

tau <- 720 ## time horizon (in days)

sim_and_true_value <- tar_map(
    values = values,
    tar_target(
        true_value,
        {
            d_int <- simulate_simple_continuous_time_data(n = 2500000,
                                                          static_intervention = 1,
                                                          no_competing_events = TRUE, 
                                                          effects = vary_effect(
                                                              effect_A_on_Y,
                                                              effect_L_on_Y,
                                                              effect_L_on_A
                                                          ))
            data.table(value = calculate_mean(d_int, tau), 
                       effect_A_on_Y = effect_A_on_Y,
                       effect_L_on_Y = effect_L_on_Y,
                       effect_L_on_A = effect_L_on_A)
        }
    ),
    tar_rep(results,
            simulate_and_run_simple(n = 1000,
                                    function_name = debias_ice_ipcw,
                                    simulate_args = list(uncensored = TRUE,
                                                         no_competing_events = TRUE,
                                                         effects = vary_effect(
                                                             effect_A_on_Y,
                                                             effect_L_on_Y,
                                                             effect_L_on_A
                                                         )),
                                    add_info = data.table(effect_A_on_Y = effect_A_on_Y,
                                                          effect_L_on_Y = effect_L_on_Y,
                                                          effect_L_on_A = effect_L_on_A),
                                    function_args = list(
                                        tau = tau,
                                        model_pseudo_outcome = "quasibinomial",
                                        model_treatment = "learn_glm_logistic",
                                        model_hazard = NA,
                                        time_covariates = time_covariates,
                                        baseline_covariates = baseline_covariates,
                                        conservative = TRUE
                                    ),
                                    function_name_2 = apply_rtmle,
                                    function_args_2 = list(
                                        tau = tau,
                                        grid_size = 8,
                                        time_confounders = setdiff(time_covariates, "A"),
                                        time_confounders_baseline = "L_0",
                                        baseline_confounders = baseline_covariates,
                                        learner = "learn_glmnet"
                                     )),
            reps = 500,
            batch = 10
            ))

# ######################################################################
list(
    sim_and_true_value,
    ## combine results
    tar_combine(
        sim_combine,
        sim_and_true_value[["results"]],
        command = dplyr::bind_rows(!!!.x, .id = "method")
    ),
    ## combine true value
    tar_combine(
        true_value_combined,
        sim_and_true_value[["true_value"]],
        command = dplyr::bind_rows(!!!.x, .id = "method")
    ),
    ## merge the true values with the debiased results by effect_A_on_Y, effect_L_on_Y, effect_L_on_A
    tar_target(
        sim_merge,
        merge(sim_combine, true_value_combined,
              by = c("effect_A_on_Y", "effect_L_on_Y", "effect_L_on_A"))
    ),
    ## calculate coverage
    tar_target(
        results_table,
        {
            sim_merge[, cov := (value > lower) & (value < upper)]
            res_cov <-sim_merge[, .(coverage = mean(cov)), 
                                by = .(effect_A_on_Y, effect_L_on_Y, effect_L_on_A, type)]
            res_se <- sim_merge[, .(SEmean = mean(se)), 
                                by = .(effect_A_on_Y, effect_L_on_Y, effect_L_on_A, type)]
            res_mse <- sim_merge[, .(mse = mean((estimate-value)^2)), 
                                 by = .(effect_A_on_Y, effect_L_on_Y, effect_L_on_A, type)]
            list(res_cov = res_cov, res_se = res_se, res_mse = res_mse)
        }
    ),
    ## boxplot the debiased results
    tar_target(
        boxplot_results,
        fun_boxplot(sim_merge, by = c("effect_A_on_Y", "effect_L_on_Y", "effect_L_on_A"))
    ),
    ## drop out plot
    tar_target(
        dropout_plot,
        plot_dropout(n = 10000, values = values, max_fup = 900)
    )

    ## descriptive statistics
    
    ## vary prevalence

    ## vary dropout
)
# ######################################################################
