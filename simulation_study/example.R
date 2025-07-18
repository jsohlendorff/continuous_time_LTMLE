### example.R --- 
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun  6 2025 (11:34) 
## Version: 
## Last-Updated: Jun 27 2025 (17:06) 
##           By: Johan Sebastian Ohlendorff
##     Update #: 357
#----------------------------------------------------------------------
## 
### Commentary: 
## 
### Change Log:
#----------------------------------------------------------------------
## 
### Code:
library(survival)
library(data.table)
library(targets)
library(rtmle) ## !!!REQUIRES NEW VERSION!!! 
library(riskRegression)
try(setwd("~/phd/continuous_time_LTMLE/simulation_study"))
try(setwd("~/research/SuperVision/Johan/continuous_time_LTMLE/simulation_study/"))
try(setwd(here::here("simulation_study")))
tar_source("functions")

tau <- 720 # time horizon in days
n <- 1000 # number of individuals
n_true_value <- 1000000 # number of individuals for true value calculation

# First compute the true value 
data_continuous_intervention <- simulate_simple_continuous_time_data(n = n_true_value,
                                                                     no_competing_events = TRUE,
                                                                     static_intervention = 1)
calculate_mean(data_continuous_intervention, tau = tau)

# Simulate continuous time data with continuous and irregular event times
data_continuous <- simulate_simple_continuous_time_data(n = n,
                                                        no_competing_events = TRUE,
                                                        uncensored = TRUE)

# Run debiased ICE-IPCW procedure
debias_ice_ipcw(data = copy(data_continuous),
                tau = tau,
                model_pseudo_outcome = "quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = NULL,
                time_covariates = c("A", "L"),
                baseline_covariates = c("age", "A_0", "L_0"),
                conservative = TRUE)

apply_rtmle( copy(data_continuous),
            tau = tau,
            grid_size = 3,
            time_confounders = "L",
            time_confounders_baseline = "L_0",
            baseline_confounders = "age",
            learner = "learn_glmnet")

apply_rtmle( copy(data_continuous),
            tau = tau,
            grid_size = 10,
            time_confounders = "L",
            time_confounders_baseline = "L_0",
            baseline_confounders = "age",
            learner = "learn_glmnet")

## Confounding maybe not so strong in the example ... 
naive_cox(data = copy(data_continuous),
          tau = tau,
          baseline_confounders = c("age", "A_0", "L_0"))

## ATE; K=1
data_continuous_ate <- simulate_continuous_time_data(n = n, K = 1)

debias_ice_ipcw(data = copy(data_continuous_ate),
                tau = tau,
                model_pseudo_outcome = "scaled_quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = c("A", "L1", "L2"),
                baseline_covariates = c("sex", "age", "A_0", "L_01", "L_02"),
                conservative = FALSE)

run_ate(data_continuous_ate, tau = tau)

## Compare run times between ate (riskRegression) and debiased ICE-IPCW (rtmle)
library(microbenchmark)

microbenchmark(
    run_ate(data_continuous_ate, tau = tau),
    debias_ice_ipcw(data = copy(data_continuous_ate),
                tau = tau,
                model_pseudo_outcome = "scaled_quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = c("A", "L1", "L2"),
                baseline_covariates = c("sex", "age", "A_0", "L_01", "L_02"),
                conservative = FALSE)
    , times = 1)

## Simulated purchase history data
## True value
set.seed(1234)
data_continuous_intervention <- simulate_continuous_time_purchase_history_data(n = n_true_value,
                                                                     no_competing_events = TRUE,
                                                                     effects = vary_effects_simple(),
                                                                     static_intervention = 1,
                                                                     days_for_medicine = 200 ## How many days can the patient take the medicine?
                                                                     )
calculate_mean(data_continuous_intervention, tau = tau)

# Simulate purchase history data 
set.seed(1234)
data_continuous <- simulate_continuous_time_purchase_history_data(n = n,
                                                        no_competing_events = TRUE,
                                                        effects = vary_effects_simple(),
                                                        uncensored = TRUE,
                                                        days_for_medicine = 200,  ## How many days can the patient take the medicine?
                                                        keep_A = TRUE)

## Full access to treatment
data_continuous_A <- data_continuous
data_continuous_A$timevarying_data <- data_continuous_A$timevarying_data[event!="M"]
debias_ice_ipcw(data = copy(data_continuous_A),
                tau = tau,
                model_pseudo_outcome = "quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = NULL,
                time_covariates = c("A", "L"),
                baseline_covariates = c("age", "A_0", "L_0"),
                conservative = TRUE)

## Reconstruct A from purchase history
data_continuous_M <- reconstruct_A_from_purchase_history(data_continuous,
                                                         med_length=200,
                                                         grace_period = 7)
debias_ice_ipcw(data = copy(data_continuous_M),
                tau = tau,
                model_pseudo_outcome = "quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = NULL,
                time_covariates = c("A", "L"),
                baseline_covariates = c("age", "A_0", "L_0"),
                conservative = TRUE)

######################################################################
### example.R ends here
