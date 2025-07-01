### discretize_time.R ---
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun 18 2025 (17:08)
## Version:
## Last-Updated: Jun 24 2025 (17:27)
##           By: Johan Sebastian Ohlendorff
##     Update #: 20
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

discretize_time <- function(data_continuous,
                            time_confounders = c("L_1", "L_2"),
                            time_confounders_baseline = c("L_01", "L_02"),
                            baseline_confounders = c("sex", "age"),
                            tau,
                            grid_size = 10) {
  n <- nrow(data_continuous$baseline_data)
  time_seq <- seq(0, tau, length.out = grid_size)
  grid <- as.data.table(expand.grid(
    id = 1:n, time = time_seq
  ))
  tau_discrete <- length(time_seq) - 1

  timevarying_baseline_data <- data_continuous$baseline_data[, c("id", "A_0", time_confounders_baseline), with = FALSE]
  timevarying_baseline_data[, c("time", "event") := list(0, "base")]
  timevarying_baseline_data[, c("Y", "Dead") := 0]
  timevarying_baseline_data[, c("Censored") := "uncensored"]
  setnames(timevarying_baseline_data, c("A_0", time_confounders_baseline), c("A", time_confounders))
  timevarying_baseline_data[, c("A", time_confounders) := lapply(.SD, factor), .SDcols = c("A", time_confounders)]

  timevarying_data <- data_continuous$timevarying_data
  timevarying_data[event == "Y", c("Y", "Dead") := list(1, 0)]
  timevarying_data[event == "D", c("Y", "Dead") := list(0, 1)]
  timevarying_data[event == "C", Censored := "censored"]
  timevarying_data[event != "C", Censored := "uncensored"]
  timevarying_data[event %in% c("A", "L"), c("Y", "Dead") := list(0, 0)]
  timevarying_data <- rbind(timevarying_data, timevarying_baseline_data)
  timevarying_data[, event := NULL]
  timevarying_data <- timevarying_data[grid, roll = TRUE, on = c("id", "time")]
  timevarying_data[, time := .GRP - 1, by = time]
  timevarying_data <- dcast(timevarying_data, id ~ time, value.var = c("Y", "Dead", "Censored", "A", time_confounders))
  timevarying_data[, c("Dead_0", "Censored_0", "Y_0") := NULL]

  outcome_data <- timevarying_data[, grepl("Y_|Dead_|Censored_|id", names(timevarying_data)), with = FALSE]
  timevar_data <- list()
  timevar_data$A <- timevarying_data[, grepl("A_|id", names(timevarying_data)), with = FALSE]
  for (v in time_confounders) {
    timevar_data[[v]] <- timevarying_data[, grepl(paste0(v, "_|id"), names(timevarying_data)), with = FALSE]
  }
  baseline_data <- data_continuous$baseline_data[, c("id", baseline_confounders), with = FALSE]
  list(
    timevar_data = timevar_data,
    outcome_data = outcome_data,
    baseline_data = baseline_data,
    tau_discrete = tau_discrete
  )
}

######################################################################
### discretize_time.R ends here
