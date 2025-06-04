## Function to get rid of the pesky .x, .y values in the column names after merging data.tables
## But also handles the cases, where either x or y is NULL
safe_merge <- function(x, y, by) {
  if (is.null(x)) {
    return(y)
  } else if (is.null(y)) {
    return(x)
  } else {
    z <- merge(x, y, by = by)
    ## Add the columns of cens_mg and Qs together if they exist
    if (all(c("cens_mg", "Q") %in% names(x) &
            c("cens_mg", "Q") %in% names(y))) {
      z[, cens_mg := cens_mg.x + cens_mg.y]
      z[, Q := Q.x + Q.y]
      z[, c("cens_mg.x", "cens_mg.y", "Q.x", "Q.y") := NULL]
    }
    return(z)
  }
}

# Function to widen continuous data from the long format to the wide format
widen_continuous_data <- function(data) {
  last_event_number <- max(data$timevarying_data$event_number)
  data_wide <- data.table::dcast(data$timevarying_data,
                                 id ~ event_number,
                                 value.var = c("time", "event", "A", "L"))
  ## Merge with baseline data
  data_wide <- merge(data_wide, data$baseline_data, by = "id")
  list(data_wide = data_wide, last_event_number = last_event_number)
}
