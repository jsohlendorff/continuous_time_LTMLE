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
                 "rtmle"),
    controller = crew_controller_local(workers = 8)
)

tar_source("functions")
time_covariates <- c("A", "L1", "L2")
baseline_covariates <- c("sex", "age", "A_0", "L_01", "L_02")
tau <- 90 ## time horizon (in days)

values <- data.frame(conservative = c(TRUE, TRUE, TRUE, TRUE),
                     uncensored = c(TRUE, TRUE, FALSE, FALSE),
                     model_hazard = c(NA, NA, "learn_coxph", "learn_coxph"),
                     model_pseudo_outcome = c("quasibinomial","quasibinomial", "tweedie", "scaled_quasibinomial"))

## Controlling coefficients for no effect
effects_no_effect <- list(
    alpha_A_0 = list(intercept = 0,
                     sex = 0,
                     age = 0,
                     L_01 = 0,
                     L_02 = 0),
    alpha_A_k = list(
        intercept = 0,
        A = 0,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0),
    alpha_L_k = list(
        intercept = 0,
        A = 0,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0),
    beta_l = list(
        A = 0,
        L1 = 0,
        L2 =  0,
        sex =  0,
        age = 0
    ),
    beta_c = list(
        A = 0,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0
    ),
    beta_y = list(
        A = 0,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0
    ),
    beta_d = list(
        A = 0,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0))

## Controlling coefficients for some effect of treatment but no effect of time-varying confounders
effects_no_effect_confounding <- list(
    alpha_A_0 = list(intercept = 0,
                     sex = 0,
                     age = 0,
                     L_01 = 0,
                     L_02 = 0),
    alpha_A_k = list(
        intercept = 0,
        A = 0.2,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0),
    alpha_L_k = list(
        intercept = 0,
        A = -0.4,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0),
    beta_l = list(
        A = 0,
        L1 = 0,
        L2 =  0,
        sex =  0,
        age = 0
    ),
    beta_c = list(
        A = 0.5,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0
    ),
    beta_y = list(
        A = 0.4,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0
    ),
    beta_d = list(
        A = 0.4,
        L1 = 0,
        L2 = 0,
        sex = 0,
        age = 0))

## Controlling coefficients for some effect of treatment and time-varying confounders
effects_some_confounding =
    list(
        alpha_A_0 = list(intercept = 0,
                         sex = 0,
                         age = 0,
                         L_01 = 0.2,
                         L_02 = 0),
        alpha_A_k = list(
            intercept = 0,
            A = 0,
            L1 = 0.1,
            L2 = 0,
            sex = 0,
            age = 0),
        alpha_L_k = list(
            intercept = 0,
            A = 0,
            L1 = 0,
            L2 = 0,
            sex = 0,
            age = 0),
        beta_l = list(
            A = -0.2,
            L1 = 0.05,
            L2 =  0,
            sex =  0,
            age = 0
        ),
        beta_c = list(
            A = 0,
            L1 = 0,
            L2 = 0,
            sex = 0,
            age = 0
        ),
        beta_y = list(
            A = - 0.9,
            L1 = 0.3,
            L2 = 0,
            sex = 0,
            age = 0
        ),
        beta_d = list(
            A = -0.8,
            L1 = 0.25,
            L2 = 0,
            sex = 0,
            age = 0))


# ######################################################################
list(
    ## Calculate mean interventional value corresponding to P_G(T <= tau and D = 1)
    tar_target(true_value_three_event, {
        d_int <- simulate_continuous_time_data(n = 2500000, static_intervention = 1, K=3)
        calculate_mean(d_int, tau)
    }),
    ## Apply debiased ICE-IPCW procedure in this situation
    tar_map_rep(
        name = debias_ipcw,
        command = simulate_and_run(
            n = 1000,
            K = 3,
            function_name = debias_ice_ipcw,
            uncensored = uncensored,
            function_args = list(
                tau = tau,
                model_pseudo_outcome = model_pseudo_outcome,
                model_treatment = "learn_glm_logistic",
                model_hazard = model_hazard,
                time_covariates = time_covariates,
                baseline_covariates = baseline_covariates,
                conservative = conservative
            )
        ),
        values = values,
        reps = 100,
        batch = 10
    ),
    ## LTMLE (vary grid size)
    tar_map_rep(
        name = ltmle_grid,
        command = simulate_and_run(n = 1000,
                                   K = 3,
                                   function_name = apply_rtmle,
                                   uncensored = uncensored,
                                   function_args = list(
                                       tau = tau,
                                       grid_size = grid_size,
                                       time_confounders = setdiff(time_covariates, "A"),
                                       time_confounders_baseline = c("L_01", "L_02"),
                                       baseline_confounders = baseline_covariates,
                                       learner = "learn_glmnet"
                                   )),
        values = expand.grid(grid_size = c(3, 5, 10), uncensored = c(TRUE, FALSE)),
        reps = 100,
        batch = 10
    ),
    ## true value (test)
    tar_target(true_value_three_event_test, {
        d_int <- simulate_continuous_time_data(n = 2500000, static_intervention = 1, K=3,
                                               effects = effects_no_effect)
        calculate_mean(d_int, tau)
    }),
    ## Apply procedure under no effects at all; replace with tar_map_rep and consider also uncensored=FALSE
    tar_map_rep(
        name = debias_ipcw_test,
        command = simulate_and_run(
            n = 1000,
            K = 3,
            function_name = debias_ice_ipcw,
            uncensored = uncensored,
            effects = effects_no_effect,
            function_args = list(
                tau = tau,
                model_pseudo_outcome = model_pseudo_outcome,
                model_treatment = "learn_glm_logistic",
                model_hazard = model_hazard,
                time_covariates = time_covariates,
                baseline_covariates = baseline_covariates,
                conservative = TRUE
            )
        ),
        values = data.frame(
            model_hazard = c(NA, "learn_coxph"),
            model_pseudo_outcome = c("quasibinomial", "scaled_quasibinomial"),
            uncensored = c(TRUE, FALSE)
        ),
        reps = 100,
        batch = 10
    ),
    ## rtmle under perfect compliance
    tar_rep(ltmle_grid_test, simulate_and_run(n = 1000,
                                               K = 3,
                                               function_name = apply_rtmle,
                                              uncensored = TRUE,
                                                  effects = effects_no_effect,
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
    ## true value (test no time varying confounders)
    tar_target(true_value_three_event_test_no_confounders, {
        d_int <- simulate_continuous_time_data(n = 2500000, static_intervention = 1, K=3,
                                               effects = effects_no_effect_confounding)
        calculate_mean(d_int, tau)
    }),
    ## Apply procedure (no time-varying confounders)
    tar_map_rep(debias_ipcw_test_no_confounders,
                simulate_and_run(n = 1000,
                                 K = 3,
                                 function_name = debias_ice_ipcw,
                                 uncensored = uncensored,
                                 effects = effects_no_effect_confounding,
                                 function_args = list(
                                     tau = tau,
                                     model_pseudo_outcome = model_pseudo_outcome,
                                     model_treatment = "learn_glm_logistic",
                                     model_hazard = model_hazard,
                                     time_covariates = time_covariates,
                                     baseline_covariates = baseline_covariates,
                                     conservative = TRUE
                                 )),
                values = data.frame(
                    model_hazard = c(NA, "learn_coxph"),
                    model_pseudo_outcome = c("quasibinomial", "scaled_quasibinomial"),
                    uncensored = c(TRUE, FALSE)
                ),
                reps = 100,
                batch = 10),
    ## true value (three events, some confounding)
    tar_target(true_value_three_event_some_confounding, {
        d_int <- simulate_continuous_time_data(n = 2500000, static_intervention = 1, K=3,
                                               effects = effects_some_confounding)
        calculate_mean(d_int, 170)
    }),
    ## Apply procedure (some confounding)
    tar_map_rep(debias_ipcw_test_some_confounding,
                simulate_and_run(n = 1000,
                                 K = 3,
                                 function_name = debias_ice_ipcw,
                                 uncensored = uncensored,
                                 effects = effects_some_confounding,
                                 function_args = list(
                                     tau = 170,
                                     model_pseudo_outcome = model_pseudo_outcome,
                                     model_treatment = "learn_glm_logistic",
                                     model_hazard = model_hazard,
                                     time_covariates = time_covariates,
                                     baseline_covariates = baseline_covariates,
                                     conservative = TRUE
                                 )),
                values = data.frame(
                    model_hazard = c(NA, "learn_coxph"),
                    model_pseudo_outcome = c("quasibinomial", "scaled_quasibinomial"),
                    uncensored = c(TRUE, FALSE)
                ),
                reps = 100,
                batch = 10),
    
    ## Boxplots for debiased IPCW estimates
    tar_target(boxplot_debias_ipcw, fun_boxplot(debias_ipcw, true_value_three_event, by = c("model_pseudo_outcome", "conservative", "uncensored", "model_hazard"))),
    ## Boxplots for LTMLE estimates
    tar_target(boxplot_ltmle_grid, fun_boxplot_rtmle(ltmle_grid, true_value_three_event, by =  c("grid_size", "uncensored"))),
    ## Boxplots for debiased IPCW estimates (test)
    tar_target(boxplot_debias_ipcw_test, fun_boxplot(debias_ipcw_test, true_value_three_event_test, by = c("model_pseudo_outcome", "uncensored", "model_hazard"))),
    ## Boxplots for LTMLE estimates (test)
    tar_target(boxplot_ltmle_grid_test, fun_boxplot_rtmle(ltmle_grid_test, true_value_three_event_test)),
    ## Boxplots for debiased IPCW estimates (test no time-varying confounders)
    tar_target(boxplot_debias_ipcw_test_no_confounders, fun_boxplot(debias_ipcw_test_no_confounders, true_value_three_event_test_no_confounders, by = c("model_pseudo_outcome", "uncensored", "model_hazard"))),
    ## Boxplots for debiased IPCW estimates (some confounding)
    tar_target(boxplot_debias_ipcw_test_some_confounding, fun_boxplot(debias_ipcw_test_some_confounding, true_value_three_event_some_confounding, by = c("model_pseudo_outcome", "uncensored", "model_hazard")))
)
# ######################################################################
