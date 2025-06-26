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
    effect_A_on_Y = c(-0.15, 0, 0.15, -0.15, -0.15, -0.15, -0.15, -0.15, 0, 0.15, -0.4, 0.4, -0.15, 0, 0.15, -0.15, -0.15),
    effect_L_on_Y = c(0.25, 0.25, 0.25, -0.25, 0, 0.25, 0.25, 0, 0, 0, 0.5,0.5,0,0,0, 0.25, 0.25),
    effect_L_on_A = c(-0.1, -0.1, -0.1, -0.1, -0.1,0, 0.1, 0, 0, 0,-0.3,0.3,0,0,0, -0.1, -0.1),
    effect_A_on_L =  c(rep(-0.2, 15), 0, 0.2),
    effect_age_on_Y = c(rep(0.025, 12), rep(0, 3), rep(0.025, 2)),
    effect_age_on_A = c(rep(0.002, 12), rep(0, 3), rep(0.002, 2))
)

tau <- 720 ## time horizon (in days)

reps <- 100 ## number of repetitions for each simulation
batches <- 50 ## number of batches to run in parallel

n_fixed <- 1000 ## number of observations for each simulation
n_true_value <- 2500000 ## number of observations for the true value estimation

by_vars <- c("effect_A_on_Y", "effect_L_on_Y", "effect_L_on_A", "effect_A_on_L", "effect_age_on_Y", "effect_age_on_A") ##  variables to group by in many results

sim_and_true_value <- tar_map(
    values = values,
    tar_target(
        true_value,
        {
            d_int <- simulate_simple_continuous_time_data(n = n_true_value,
                                                          static_intervention = 1,
                                                          no_competing_events = TRUE, 
                                                          effects = vary_effect(
                                                              effect_A_on_Y,
                                                              effect_L_on_Y,
                                                              effect_L_on_A,
                                                              effect_A_on_L,
                                                              effect_age_on_Y,
                                                              effect_age_on_A
                                                          ))
            data.table(value = calculate_mean(d_int, tau), 
                       effect_A_on_Y = effect_A_on_Y,
                       effect_L_on_Y = effect_L_on_Y,
                       effect_L_on_A = effect_L_on_A,
                       effect_A_on_L = effect_A_on_L,
                       effect_age_on_Y = effect_age_on_Y,
                       effect_age_on_A = effect_age_on_A)
        }
    ),
    tar_rep(results,
            simulate_and_run_simple(n = n_fixed,
                                    function_name = debias_ice_ipcw,
                                    simulate_args = list(uncensored = TRUE,
                                                         no_competing_events = TRUE,
                                                         effects = vary_effect(
                                                             effect_A_on_Y,
                                                             effect_L_on_Y,
                                                             effect_L_on_A,
                                                             effect_A_on_L,
                                                             effect_age_on_Y,
                                                             effect_age_on_A
                                                         )),
                                    add_info = data.table(effect_A_on_Y = effect_A_on_Y,
                                                          effect_L_on_Y = effect_L_on_Y,
                                                          effect_L_on_A = effect_L_on_A,
                                                          effect_A_on_L = effect_A_on_L,
                                                          effect_age_on_Y = effect_age_on_Y,
                                                          effect_age_on_A = effect_age_on_A),
                                    function_args = list(
                                        tau = tau,
                                        model_pseudo_outcome = "quasibinomial",
                                        model_treatment = "learn_glm_logistic",
                                        model_hazard = NA,
                                        time_covariates = time_covariates,
                                        baseline_covariates = baseline_covariates,
                                        conservative = TRUE
                                    ),
                                    function_nice_names = c("Debiased ICE-IPCW",
                                                            "LTMLE (grid size = 5)",
                                                            "Naive Cox"),
                                    function_name_2 = apply_rtmle,
                                    function_args_2 = list(
                                        tau = tau,
                                        grid_size = 5,
                                        time_confounders = setdiff(time_covariates, "A"),
                                        time_confounders_baseline = "L_0",
                                        baseline_confounders = baseline_covariates,
                                        learner = "learn_glmnet"
                                    ),
                                    function_name_3 = naive_cox,
                                    function_args_3 = list(
                                        tau = tau,
                                        baseline_confounders = baseline_covariates
                                    )),
            reps = reps,
            batch = batches
            ),
    ## censored case
    tar_rep(results_censored,
            simulate_and_run_simple(n = n_fixed,
                                    function_name = debias_ice_ipcw,
                                    simulate_args = list(uncensored = FALSE,
                                                         no_competing_events = TRUE,
                                                         effects = vary_effect(
                                                             effect_A_on_Y,
                                                             effect_L_on_Y,
                                                             effect_L_on_A,
                                                             effect_A_on_L,
                                                             effect_age_on_Y,
                                                             effect_age_on_A
                                                         )),
                                    add_info = data.table(effect_A_on_Y = effect_A_on_Y,
                                                          effect_L_on_Y = effect_L_on_Y,
                                                          effect_L_on_A = effect_L_on_A,
                                                          effect_A_on_L = effect_A_on_L,
                                                          effect_age_on_Y = effect_age_on_Y,
                                                          effect_age_on_A = effect_age_on_A),
                                    function_args = list(
                                        tau = tau,
                                        model_pseudo_outcome = "scaled_quasibinomial",
                                        model_treatment = "learn_glm_logistic",
                                        model_hazard = "learn_coxph",
                                        time_covariates = time_covariates,
                                        baseline_covariates = baseline_covariates,
                                        conservative = TRUE
                                    )),
            reps = reps,
            batch = batches
            )
)

## vary prevalence
sim_and_true_value_prevalence <- tar_map(
    values = data.frame(baseline_rate_Y =  c(0.00005, 0.0001, 0.0002)),
    tar_target(
        true_value_prevalence,
        {
            d_int <- simulate_simple_continuous_time_data(n = n_true_value,
                                                          static_intervention = 1,
                                                          no_competing_events = TRUE,
                                                          baseline_rate_list = list(
                                                              A = 0.005,
                                                              L = 0.001,
                                                              C = 0.00005,
                                                              Y = baseline_rate_Y,
                                                              D = 0.00015
                                                          ))
            data.table(value = calculate_mean(d_int, tau), 
                       baseline_rate_Y = baseline_rate_Y)
        }
    ),
    tar_rep(results_prevalence,
            simulate_and_run_simple(n = n_fixed,
                                    function_name = debias_ice_ipcw,
                                    simulate_args = list(uncensored = TRUE,
                                                         no_competing_events = TRUE,
                                                         baseline_rate_list = list(
                                                             A = 0.005,
                                                             L = 0.001,
                                                             C = 0.00005,
                                                             Y = baseline_rate_Y,
                                                             D = 0.00015
                                                         )),
                                    add_info = data.table(baseline_rate_Y = baseline_rate_Y),
                                    function_args = list(
                                        tau = tau,
                                        model_pseudo_outcome = "quasibinomial",
                                        model_treatment = "learn_glm_logistic",
                                        model_hazard = NA,
                                        time_covariates = time_covariates,
                                        baseline_covariates = baseline_covariates,
                                        conservative = TRUE
                                    )),
            reps = reps,
            batch = batches
            )
)

## vary dropout
sim_and_true_value_dropout <- tar_map(
    values = data.frame(a_intercept = c(-2.5,-1.1,-0.5, 0.3, 1.1)),
    tar_target(
        true_value_dropout,
        {
            d_int <- simulate_simple_continuous_time_data(n = n_true_value,
                                                          static_intervention = 1,
                                                          no_competing_events = TRUE, 
                                                          effects = vary_dropout(
                                                              a_intercept = a_intercept
                                                          ))
            data.table(value = calculate_mean(d_int, tau),
                       a_intercept = a_intercept)
        }
    ),
    tar_rep(results_dropout,
            simulate_and_run_simple(n = n_fixed,
                                    function_name = debias_ice_ipcw,
                                    simulate_args = list(uncensored = TRUE,
                                                         no_competing_events = TRUE,
                                                         effects = vary_dropout(
                                                             a_intercept = a_intercept
                                                         )),
                                    add_info = data.table(a_intercept = a_intercept),
                                    function_args = list(
                                        tau = tau,
                                        model_pseudo_outcome = "quasibinomial",
                                        model_treatment = "learn_glm_logistic",
                                        model_hazard = NA,
                                        time_covariates = time_covariates,
                                        baseline_covariates = baseline_covariates,
                                        conservative = TRUE
                                    )),
            reps = reps,
            batch = batches
            )
)

## vary sample size
sim_sample_size <- tar_map(
    values = data.frame(n = c(100,200,500,1000),
                        effect_A_on_Y = c(-0.15, -0.15, -0.15, -0.15),
                        effect_L_on_Y = c(0.25, 0.25, 0.25, 0.25),
                        effect_L_on_A = c(-0.1, -0.1, -0.1, -0.1),
                        effect_A_on_L = c(-0.2, -0.2, -0.2, -0.2),
                        effect_age_on_Y = c(0.025, 0.025, 0.025, 0.025),
                        effect_age_on_A = c(0.002, 0.002, 0.002, 0.002)),    
    tar_rep(results_sample_size,
            simulate_and_run_simple(n = n,
                                    function_name = debias_ice_ipcw,
                                    simulate_args = list(uncensored = TRUE,
                                                         no_competing_events = TRUE,
                                                         effects = vary_effect(
                                                             effect_A_on_Y,
                                                             effect_L_on_Y,
                                                             effect_L_on_A,
                                                             effect_A_on_L,
                                                             effect_age_on_Y,
                                                             effect_age_on_A
                                                         )),
                                    add_info = data.table(n = n,
                                                          effect_A_on_Y = effect_A_on_Y,
                                                          effect_L_on_Y = effect_L_on_Y,
                                                          effect_L_on_A = effect_L_on_A,
                                                          effect_A_on_L = effect_A_on_L,
                                                          effect_age_on_Y = effect_age_on_Y,
                                                          effect_age_on_A = effect_age_on_A),
                                    function_args = list(
                                        tau = tau,
                                        model_pseudo_outcome = "quasibinomial",
                                        model_treatment = "learn_glm_logistic",
                                        model_hazard = NA,
                                        time_covariates = time_covariates,
                                        baseline_covariates = baseline_covariates,
                                        conservative = TRUE
                                    )),
            reps = reps,
            batch = batches
            )
)

# ######################################################################
list(
    ## drop out plot (varying intercept; see how well method performs under practical positivity violation conditions)
    tar_target(
        dropout_plot_vary,
        plot_dropout_vary(n = 10000, values = data.frame(a_intercept = c(-2.5,-1.2,-0.5, 0.3, 1.1)), max_fup = 900)
    ),
    ## drop out plot (for varying coefficients)
    tar_target(
        dropout_plot,
        plot_dropout(n = 10000, values = values, max_fup = 900)
    ),
    ## support for ice_ipcw; do we have enough people at risk after each event point?
    tar_target(
        support_ice_ipcw,
        support_ice(values = values, tau = tau, large_n = 100000, no_competing_event = TRUE)
    ),
    
    ## simulate 
    sim_and_true_value,
    ## combine results
    tar_combine(
        sim_merge,
        list(sim_and_true_value[["results"]],
             sim_and_true_value[["true_value"]]),
        command = combine_results_and_true_values(!!!.x, .id = "method", by = by_vars)
    ),
    ## merge the true values with the debiased results for the censored case
    tar_combine(
        sim_merge_censored,
        list(sim_and_true_value[["results_censored"]],
             sim_and_true_value[["true_value"]]),
        command = combine_results_and_true_values(!!!.x, .id = "method", by = by_vars)
    ),
    
    ## calculate coverage
    tar_target(
        results_table, get_tables(sim_merge, 
                                  by = by_vars)
    ),
    ## calculate coverage for the censored case
    tar_target(
        results_table_censored, get_tables(sim_merge_censored, 
                                           by = by_vars)
    ),
    ## boxplot the debiased results (no confounding)
    tar_target(
        boxplot_results_no_confounding,
        fun_boxplot(sim_merge[effect_L_on_Y == 0 & effect_L_on_A == 0 & effect_age_on_Y == 0 & effect_age_on_A == 0]
                  , by = by_vars
                  )
    ),
    ## boxplot the debiased results (no confounding; censored)
    tar_target(
        boxplot_results_censored_no_confounding,
        fun_boxplot(sim_merge_censored[effect_L_on_Y == 0 & effect_L_on_A == 0 & effect_age_on_Y == 0 & effect_age_on_A == 0]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (strong confounding)
    tar_target(
        boxplot_results_strong_time_confounding,
        fun_boxplot(sim_merge[effect_L_on_Y == 0.5]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (strong confounding; censored)
    tar_target(
        boxplot_results_censored_strong_time_confounding,
        fun_boxplot(sim_merge_censored[effect_L_on_Y == 0.5]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (no time confounding, but baseline confounding)
    tar_target(
        boxplot_results_no_time_confounding,
        fun_boxplot(sim_merge[effect_L_on_Y == 0 & effect_L_on_A == 0 & effect_age_on_Y != 0 & effect_age_on_A != 0]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (no time confounding, but baseline confounding; censored)
    tar_target(
        boxplot_results_censored_no_time_confounding,
        fun_boxplot(sim_merge_censored[effect_L_on_Y == 0 & effect_L_on_A == 0 & effect_age_on_Y != 0 & effect_age_on_A != 0]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_A_on_Y)
    tar_target(
        boxplot_results_vary_effect_A_on_Y,
        fun_boxplot(sim_merge[effect_L_on_Y == 0.25 & effect_L_on_A == -0.1 & 
                     effect_A_on_L == -0.2]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_A_on_Y; censored)
    tar_target(
        boxplot_results_censored_vary_effect_A_on_Y,
        fun_boxplot(sim_merge_censored[effect_L_on_Y == 0.25 & effect_L_on_A == -0.1 & 
                     effect_A_on_L == -0.2]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_L_on_Y)
    tar_target(
        boxplot_results_vary_effect_L_on_Y,
        fun_boxplot(sim_merge[effect_A_on_Y == -0.15 & effect_L_on_A == -0.1 & 
                     effect_A_on_L == -0.2]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_L_on_Y; censored)
    tar_target(
        boxplot_results_censored_vary_effect_L_on_Y,
        fun_boxplot(sim_merge_censored[effect_A_on_Y == -0.15 & effect_L_on_A == -0.1 & effect_A_on_L == -0.2]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_L_on_A)
    tar_target(
        boxplot_results_vary_effect_L_on_A,
        fun_boxplot(sim_merge[effect_A_on_Y == -0.15 & effect_L_on_Y == 0.25 & effect_A_on_L == -0.2]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_L_on_A; censored)
    tar_target(
        boxplot_results_censored_vary_effect_L_on_A,
        fun_boxplot(sim_merge_censored[effect_A_on_Y == -0.15 & effect_L_on_Y == 0.25 & effect_A_on_L == -0.2]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_A_on_L)
    tar_target(
        boxplot_results_vary_effect_A_on_L,
        fun_boxplot(sim_merge[effect_A_on_Y == -0.15 & effect_L_on_Y == 0.25 & effect_L_on_A == -0.1]
                  , by = by_vars)
    ),
    ## boxplot the debiased results (vary effect_A_on_L; censored)
    tar_target(
        boxplot_results_censored_vary_effect_A_on_L,
        fun_boxplot(sim_merge_censored[effect_A_on_Y == -0.15 & effect_L_on_Y == 0.25 & effect_L_on_A == -0.1]
                  , by = by_vars)
    ),
    
    ## vary prevalence
    sim_and_true_value_prevalence,
    tar_combine(
        sim_merge_prevalence,
        list(sim_and_true_value_prevalence[["results_prevalence"]],
             sim_and_true_value_prevalence[["true_value_prevalence"]]),
        command = combine_results_and_true_values(!!!.x, .id = "method", by = "baseline_rate_Y")
    ),
    tar_target(
        results_table_prevalence, get_tables(sim_merge_prevalence, by = "baseline_rate_Y")
    ),
    tar_target(
        boxplot_results_prevalence,
        fun_boxplot(sim_merge_prevalence, by = "baseline_rate_Y")
    ),
    
    ## vary dropout
    sim_and_true_value_dropout,
    tar_combine(
        sim_merge_dropout,
        list(sim_and_true_value_dropout[["results_dropout"]],
             sim_and_true_value_dropout[["true_value_dropout"]]),
        command = combine_results_and_true_values(!!!.x, .id = "method", by = "a_intercept")
    ),
    tar_target(
        results_table_dropout, get_tables(sim_merge_dropout, by = "a_intercept")
    ),
    tar_target(
        boxplot_results_dropout,
        fun_boxplot(sim_merge_dropout, by = "a_intercept")
    ),

    ## ## vary sample size
    sim_sample_size,
    ##v tar combine
    tar_combine(
        sim_merge_sample_size,
        list(sim_sample_size[["results_sample_size"]],
             sim_and_true_value[["true_value"]]),
        command = combine_results_and_true_values(!!!.x, .id = "method", by = by_vars)
    ),
    tar_target(
        results_table_sample_size, get_tables(sim_merge_sample_size, by = "n")
    ),
    tar_target(
        boxplot_results_sample_size,
        fun_boxplot(sim_merge_sample_size, by = "n")
    )
)
# ######################################################################
