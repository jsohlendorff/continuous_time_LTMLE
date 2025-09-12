### clean_and_combine.R ---
#----------------------------------------------------------------------
## author:
## created: aug 15 2025 (11:58)
## Version:
## last-updated: sep  2 2025 (14:59) 
##     Update #: 158
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

clean_and_combine <- function(dt_list_non_outcome,
                              outcome,
                              baseline,
                              treat_names = c("sglt2", "dpp4"),
                              timevar_names = "hba1c",
                              discretize_hba1c=FALSE) {
  ## tar_load(regime)
  ## tar_load(outcome)
  ## tar_load(baseline)
  ## tar_load(hba1c)
  ## dt_list_non_outcome <- list(regime, hba1c)
  ## treat_names = c("sglt2", "dpp4")
  ## timevar_names= "hba1c"
  dt <- rbindlist(append(dt_list_non_outcome, list(outcome)), use.names = TRUE)
  outcome_dt <- outcome
  setnames(outcome_dt, "time", "terminal_time")
  dt <- merge(dt, outcome_dt[, c("pnr", "terminal_time")], by = "pnr")[time <= terminal_time]

  dt$X <- factor(dt$X,
    levels = c("Y", "D", "C", timevar_names, treat_names)
  )
  setorder(dt, pnr, time, X)
  ## Generate the columns corresponding to timevarying names and treat names
  ## Carrying e.g., the last value forward
  for (med in c(timevar_names, treat_names)) {
    match_idx <- dt$X == med

    # Create a new column with val where X == med, else NA
    dt[, (med) := fifelse(match_idx, val, NA)]

    # Fill forward (last observation carried forward)
    dt[, (med) := nafill(get(med), type = "locf"), by = "pnr"]

    # Replace remaining NAs (before first match) with 0
    dt[is.na(get(med)), (med) := 0]
  }
  ## Make this line more generally usable in the future
  if (discretize_hba1c) dt$hba1c <- cut(dt$hba1c, breaks=c(-Inf,42,48,53,64, Inf), right=FALSE) ## Categorize using Kathrines categories
  ## Time zero
  dt_zero <- dt[time == 0 & X %in% treat_names]
  dt_zero[, c("X", "time", "val", "terminal_time") := NULL]
  baseline <- merge(baseline, dt_zero, by = "pnr")

  ## Time > 0
  dt_pos <- dt[time > 0]
  setnames(dt_pos, "X", "event")
  dt_pos[event %in% treat_names, event := "A"]
  dt_pos[event %in% timevar_names, event := "L"]
  dt_pos[, val := NULL]
  ## Break ties for A,L and terminal events
  dt_pos <- dt_pos[!(time == terminal_time & event %in% c("A", "L"))]
  dt_pos[, dup := duplicated(time) | duplicated(time, fromLast = TRUE), by = "pnr"]
  ## Break ties for L and A
  dt_pos[dup == TRUE & event == "A", time := time + 0.5]
  dt_pos[, c("dup", "terminal_time") := NULL]

  setnames(dt_pos, "pnr", "id")
  setnames(baseline, "pnr", "id")
  list(baseline_data = baseline, timevarying_data = dt_pos)
}

#----------------------------------------------------------------------
### clean_and_combine.R ends here
