at_risk <- function(dt, tau) {
  dt <- dt[time > 0]
  dt[, event_number := seq_len(.N), by = id]
  dt[time < tau &
    !(X %in% c("censored", "mace", "all_cause_mortality")), .N, by = "event_number"]
}
# What event number do people deviate from?
# dt[, event_number := seq_len(.N), by = id]
# dt[time < tau & X=="placebo" & placebo==0]$event_number
