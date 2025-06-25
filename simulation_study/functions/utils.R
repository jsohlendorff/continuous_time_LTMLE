## Utility functions for the package

## Wrapper function to predict the outcome under an intervention
predict_intervention <- function(data, k, predict_fun, static_intervention) {
  intervened_data <- copy(data)
  for (j in seq(0,k)) {
    intervened_data[, paste0("A_", j) := static_intervention]
  }
  # intervened_data[[paste0("event_", k)]] <- droplevels(intervened_data[[paste0("event_", k)]])
  f <- predict_fun(intervened_data)
  ## TODO: Check if the predictions are in the range [0,1]
  ## Warn if any predictions are NA or below or above 1
  if (any(is.na(f))) {
    warning("Predictions contain NA values.")
  }
  f
}

## Function to get rid of the .x, .y values in the column names after merging data.tables
## But also handles the cases where either x or y is NULL
safe_merge <- function(x, y, by) {
  if (is.null(x)) {
    y
  } else if (is.null(y)) {
    x
  } else {
    z <- merge(x, y, by = by)
    ## Add the columns of cens_mg and Qs together if they exist
    if (all(c("cens_mg", "Q") %in% names(x) &
            c("cens_mg", "Q") %in% names(y))) {
      z[, cens_mg := cens_mg.x + cens_mg.y]
      z[, Q := Q.x + Q.y]
      z[, c("cens_mg.x", "cens_mg.y", "Q.x", "Q.y") := NULL]
    }
    z
  }
}

# Function to widen continuous data from the long format to the wide format
widen_continuous_data <- function(data, time_covariates) {
  data_wide <- data.table::dcast(data$timevarying_data,
                                 id ~ event_number,
                                 value.var = c("time", "event", time_covariates))

  ## Merge with baseline data
  merge(data_wide, data$baseline_data, by = "id")
}
