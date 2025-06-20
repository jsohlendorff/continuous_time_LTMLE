### example.R --- 
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun  6 2025 (11:34) 
## Version: 
## Last-Updated: Jun 20 2025 (09:43) 
##           By: Johan Sebastian Ohlendorff
##     Update #: 163
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
library(rtmle)
library(riskRegression)
try(setwd("~/phd/continuous_time_LTMLE/simulation_study"))
tar_source("functions")

tau <- 90 # time horizon in days
n <- 1000 # number of individuals
n_true_value <- 1000000 # number of individuals for true value calculation

# First compute the true value 
data_continuous_intervention <- simulate_continuous_time_data(n = n_true_value,
                                                              static_intervention = 1,
                                                              K = 3)
calculate_mean(data_continuous_intervention, tau = tau)

# Simulate continuous time data with continuous and irregular event times
data_continuous <- simulate_continuous_time_data(n = n, K = 3)

# Run debiased ICE-IPCW procedure
debias_ice_ipcw(data = copy(data_continuous),
                tau = tau,
                model_pseudo_outcome = "scaled_quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = c("A", "L1", "L2"),
                baseline_covariates = c("sex", "age", "A_0", "L_01", "L_02"),
                conservative = TRUE)

apply_rtmle( copy(data_continuous),
            tau = tau,
            grid_size = 3,
            time_confounders = c("L1", "L2"),
            time_confounders_baseline = c("L_01", "L_02"),
            baseline_confounders = c("sex","age"),
            learner = "learn_glmnet")

apply_rtmle( copy(data_continuous),
            tau = tau,
            grid_size = 10,
            time_confounders = c("L1", "L2"),
            time_confounders_baseline = c("L_01", "L_02"),
            baseline_confounders = c("sex","age"),
            learner = "learn_glmnet")

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
