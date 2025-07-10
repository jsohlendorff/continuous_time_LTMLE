## Utility functions for the package

## Wrapper function to predict the outcome under an intervention
predict_intervention <- function(data, k, predict_fun, static_intervention) {
  intervened_data <- copy(data)
  if (k > 0) {
    intervened_data[event_k == "A", paste0("A_", k) := static_intervention, env = list(event_k = paste0("event_", k))]
  } else {
    intervened_data[, A_0 := static_intervention]
  }
  f <- predict_fun(intervened_data)
  ## TODO: Check if the predictions are in the range [0,1]
  ## Warn if any predictions are NA or below or above 1
  if (any(is.na(f))) {
    stop("Predictions contain NA values.")
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
    value.var = c("time", "event", time_covariates)
  )

  ## Merge with baseline data
  merge(data_wide, data$baseline_data, by = "id")
}

get_history_of_variables <- function(data,
                                     time_covariates,
                                     baseline_covariates,
                                     type,
                                     k_lag,
                                     k) {
  if (!is.null(k_lag) && k > 1) {
    event_points <- seq(from = max(1, k - k_lag), to = k - 1, by = 1)
  } else {
    event_points <- seq_len(k - 1)
  }

  ## Time-varying covariates to use in regressions
  if (k > 1) {
    time_history <- unlist(lapply(c(time_covariates, "time", "event"), function(x) {
      paste0(x, "_", event_points)
    }))
  } else {
    time_history <- NULL
  }
  if (type == "hazard") {
    time_history <- setdiff(time_history, paste0("time_", k - 1))
  } else if (type == "propensity") {
    ## Allow for A and L to occur at the same time
    time_history <- c(time_history, paste0("time_", k), paste0(setdiff(time_covariates, "A"), "_", k))
  } else if (type == "martingale") {
    time_history <- setdiff(time_history, paste0(setdiff(time_covariates, "A"), "_", k - 1))
  }

  ## Full history of variables, i.e., covariates used in regressions
  history_of_variables <- c(time_history, baseline_covariates)

  ## Remove variables from history_of_variables that do not have more than one value
  ## in the data
  if (!type == "martingale") {
    history_of_variables <- setdiff(
      history_of_variables,
      names(which(sapply(data[, ..history_of_variables], function(x) length(unique(x)) <= 1)))
    )
  }
  history_of_variables
}

get_at_risk_data <- function(data,
                             k,
                             is_censored,
                             marginal_hazard,
                             return_at_risk_before_tau,
                             tau = NULL) {
  if (k == 1) {
    at_risk_interevent <- at_risk_before_tau <- data
  } else {
    at_risk_interevent <- data[event_k_previous %in% c("A", "L"), env = list(event_k_previous = paste0("event_", k - 1))]
    if (nrow(at_risk_interevent) == 0) {
      return(NULL)
    }
    if (return_at_risk_before_tau) {
      at_risk_before_tau <- at_risk_interevent[time_previous < tau, env = list(time_previous = paste0("time_", k - 1))]
      if (nrow(at_risk_before_tau) == 0) {
        return(NULL)
      }
    } else {
      at_risk_before_tau <- NULL
    }
    if (is_censored && !marginal_hazard) {
      ## Shift the interevent times according to time_(k-1); makes modeling more natural
      at_risk_interevent[, paste0("time_", k) := time_k - time_k_minus_1,
        env = list(
          time_k = paste0("time_", k),
          time_k_minus_1 = paste0("time_", k - 1)
        )
      ]
      for (j in seq_len(k - 1)) {
        at_risk_interevent[, paste0("time_", j) := time_k_minus_1 - time_j,
          env = list(
            time_k_minus_1 = paste0("time_", k - 1),
            time_j = paste0("time_", j)
          )
        ]
        at_risk_interevent[, paste0("event_", j) := droplevels(event_j),
          env = list(
            event_j = paste0("event_", j)
          )
        ]
      }
    }
  }
  list(
    at_risk_interevent = at_risk_interevent,
    at_risk_before_tau = at_risk_before_tau
  )
}
