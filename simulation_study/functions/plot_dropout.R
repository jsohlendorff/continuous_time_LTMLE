### plot_dropout.R ---
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun 25 2025 (11:36)
## Version:
## Last-Updated: Jun 25 2025 (13:30)
##           By: Johan Sebastian Ohlendorff
##     Update #: 13
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

plot_dropout <- function(n = 10000, values, max_fup = 900) {
  data_all <- list()
  for (i in 1:nrow(values)) {
    effect_A_on_Y <- values$effect_A_on_Y[i]
    effect_L_on_Y <- values$effect_L_on_Y[i]
    effect_L_on_A <- values$effect_L_on_A[i]

    data_continuous <- simulate_simple_continuous_time_data(
      n = 10000, uncensored = TRUE,
      effects = vary_effect(
        effect_A_on_Y,
        effect_L_on_Y,
        effect_L_on_A
      )
    )$timevarying_data
    data_continuous[, c("effect_A_on_Y", "effect_L_on_Y", "effect_L_on_A") :=
      list(effect_A_on_Y, effect_L_on_Y, effect_L_on_A)]
    drop_out <- data_continuous[A == 0 & event == "A"]
    drop_out <- drop_out[, .(id, time, effect_A_on_Y, effect_L_on_Y, effect_L_on_A)]
    ids_drop_out <- unique(drop_out$id)
    ids_not_drop_out <- setdiff(data_continuous$id, ids_drop_out)
    not_drop_out <- data.table(
      id = ids_not_drop_out, time = 900,
      effect_A_on_Y = effect_A_on_Y,
      effect_L_on_Y = effect_L_on_Y,
      effect_L_on_A = effect_L_on_A
    )
    drop_out <- rbind(drop_out, not_drop_out)

    data_all[[i]] <- drop_out
  }

  data_all <- rbindlist(data_all)
  data_all$status <- 1
  fit <- survfit(Surv(time, status) ~ effect_A_on_Y + effect_L_on_Y + effect_L_on_A, data = data_all)
  ggsurvplot(fit, data = data_all, xlim = c(0, 800))
}

## plot drop out; vary dropout
plot_dropout_vary <- function(n = 10000, values = data.frame(a_intercept = c(-2.5, -1.2, -0.5, 0.3, 1.1)), max_fup = 900) {
  data_all <- list()
  for (i in 1:nrow(values)) {
    a_intercept <- values$a_intercept[i]

    data_continuous <- simulate_simple_continuous_time_data(
      n = 10000, uncensored = TRUE,
      effects = vary_dropout(
        a_intercept = a_intercept
      )
    )$timevarying_data
    data_continuous[, c("a_intercept") := list(a_intercept)]
    drop_out <- data_continuous[A == 0 & event == "A"]
    drop_out <- drop_out[, .(id, time, a_intercept)]
    ids_drop_out <- unique(drop_out$id)
    ids_not_drop_out <- setdiff(data_continuous$id, ids_drop_out)
    not_drop_out <- data.table(
      id = ids_not_drop_out, time = 900,
      a_intercept = a_intercept
    )
    drop_out <- rbind(drop_out, not_drop_out)

    data_all[[i]] <- drop_out
  }

  data_all <- rbindlist(data_all)
  data_all$status <- 1
  fit <- survfit(Surv(time, status) ~ a_intercept, data = data_all)
  ggsurvplot(fit, data = data_all, xlim = c(0, 800))
}

######################################################################
### plot_dropout.R ends here
