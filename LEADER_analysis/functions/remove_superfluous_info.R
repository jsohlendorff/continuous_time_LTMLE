## Function to remove superfluous information.
## We don't care if a patient stopped their treatment for less than a week and then started again.
## That is, we do not care about very short interruptions of treatment.
## Otherwise, there is simply too much information from the time-varying covariates.
## That is, if the start date of a new registration is less
## than 7 days after the end date of the previous event, we remove it
## and make one single registration that spans the two events (with start date equal
## to the first registration start date and end date equal to the last registration
## end date). Generally, we may chain together more than two events.
remove_superfluous_info_fast <- function(dt, period = 7) {
  setorder(dt, id, X, start_time)
  
  # Calculate gap for entire table (in-place)
  dt[, gap := start_time - shift(end_time, fill = as.POSIXct(0)), by = .(id, X)]
  
  # Define chain ID within id+X using cumulative sum where gap > period
  dt[, chain := cumsum(as.numeric(gap, units = "days") > period), by = .(id, X)]
  
  # Aggregate start and end times by chain
  dt[, `:=`(
    start_time = min(start_time),
    end_time = max(end_time)
  ), by = .(id, X, chain)]
  
  # Keep only the last row of each chain
  result <- dt[, .SD[.N], by = .(id, X, chain)]
  
  # Remove temp columns
  result[, `:=`(gap = NULL, chain = NULL)]
  
  return(result)
}


## Here, we keep the visitation times
remove_superfluous_info_primary_treatment <- function(x, period = 7) {
  x$val <- 1
  if (nrow(x) == 1) {
    return(x)
  }
  for (i in 2:nrow(x)) {
    if (x$start_time[i] - x$end_time[i - 1] > period) {
      ## Add new row to x with val = 0 with start_time = end_time[i-1] + 1 and end_time = start_time[i] - 1
      new_row <- data.table(
        start_time = x$end_time[i - 1] + 1,
        end_time = x$start_time[i] - 1,
        val = 0
      )
      x <- rbind(x, new_row, use.names = FALSE)
    }
  }
  x
}
