### test_against_ate.R ---
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun 19 2025 (10:22)
## Version:
## Last-Updated: Jun 19 2025 (16:21)
##           By: Johan Sebastian Ohlendorff
##     Update #: 7
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

run_ate <- function(data_continuous, tau) {
  data_full <- data.table(cbind(
    data_continuous$baseline_data,
    data_continuous$timevarying_data
  ))
  data_full <- data_full[, A := NULL]
  data_full <- data_full[, L1 := NULL]
  data_full <- data_full[, L2 := NULL]
  data_full$event <- droplevels(data_full$event)
  levels(data_full$event) <- c("0", "1", "2")
  data_full$A_0 <- factor(data_full$A_0)

  ## working models
  m.event <- CSC(Hist(time, event) ~ sex + age + A_0 + L_01 + L_02, data = data_full, cause = 1)
  m.censor <- coxph(Surv(time, event == 0) ~ sex + age + A_0 + L_01 + L_02,
    data = data_full, x = TRUE,
    y = TRUE
  )
  m.treatment <- glm(A_0 ~ sex + age + L_01 + L_02, data = data_full, family = "binomial")

  ## prediction + average
  ateRobust <- ate(
    event = m.event,
    treatment = m.treatment,
    censor = m.censor,
    data = data_full, times = tau,
    cause = 1,
    verbose = FALSE
  )
  as.data.table(ateRobust$meanRisk[treatment == "1"])
}

######################################################################
### test_against_ate.R ends here
