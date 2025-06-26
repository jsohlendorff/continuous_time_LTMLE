### naive_cox.R --- 
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun 26 2025 (11:29) 
## Version: 
## Last-Updated: Jun 26 2025 (11:34) 
##           By: Johan Sebastian Ohlendorff
##     Update #: 6
#----------------------------------------------------------------------
## 
### Commentary: 
## 
### Change Log:
#----------------------------------------------------------------------
## 
### Code:

naive_cox <- function(data_continuous, tau, baseline_confounders) {
    drop_out_data <- data_continuous$timevarying_data[event == "A" & A == 0, .(id = id, time = time)]
    drop_out_data$status <- 0
    #ids not in drop_out_data
    ids_not_dropped_out <- data_continuous$timevarying_data[!(id %in% drop_out_data$id), unique(id)]
    ## get C and Y events for these ids
    outcome_data <- data_continuous$timevarying_data[(event == "C" | event == "Y" )& id %in% ids_not_dropped_out, .(id = id, time = time,status = event)]
    ## change C to 0 and Y to 1
    outcome_data$status <- ifelse(outcome_data$status == "C", 0, 1)
    ## rbind the drop_out_data and outcome_data
    outcome_data <- rbind(drop_out_data, outcome_data, fill = TRUE)
    ## add baseline data
    outcome_data <- merge(outcome_data, data_continuous$baseline_data[, .(id, age, A_0, L_0)], by = "id", all.x = TRUE)
    ## remove baseline confounders that are constant from baseline confounders
    baseline_confounders <- baseline_confounders[sapply(outcome_data[, ..baseline_confounders], function(x) length(unique(x)) > 1)]
    form_cox <- as.formula(paste("Surv(time, status) ~", paste(baseline_confounders, collapse = " + ")))
    
    fit<-coxph(Surv(time, status) ~ age, data = outcome_data,
               x = TRUE, y = TRUE)
    data.table(estimate = mean(predictRisk(fit, newdata = outcome_data, times = tau, type = "risk")), lower = NA, upper = NA, se = NA, ice_ipcw_estimate = NA, ipw = NA)
}

######################################################################
### naive_cox.R ends here
