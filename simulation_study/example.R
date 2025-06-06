### example.R --- 
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun  6 2025 (11:34) 
## Version: 
## Last-Updated: Jun  6 2025 (11:43) 
##           By: Johan Sebastian Ohlendorff
##     Update #: 4
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
tar_source("functions")

# Simulate continuous time data with continuous and irregular event times
data_continuous <- simulate_continuous_time_data(n = 1000, number_events = 3)

# Run debiased ICE-IPCW procedure
debias_ice_ipcw(data = data_continuous,
                tau = 0.03,
                model_pseudo_outcome = "scaled_quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = c("A", "L1", "L2"),
                baseline_covariates = c("sex", "age", "A_0", "L_01", "L_02"),
                conservative = FALSE)

######################################################################
### example.R ends here
