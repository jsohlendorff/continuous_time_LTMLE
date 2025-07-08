find_terminal <- function(dt, outcomes) {
  dt[X %in% outcomes, time, by = id]
}

combine <- function(comed,
                    adv,
                    reg,
                    out,
                    outcomes = c("all_cause_mortality", "mace", "censored"),
                    treat_name,
                    id_regimen) {
  # comed<-tar_read(comedication_cleaned)
  # adv<-tar_read(adverse_events_cleaned)
  # reg<-tar_read(regime_cleaned)
  # out <-tar_read(outcome_cleaned)
  # id_regimen <- tar_read(id_regimen_lira)
  adverse_event_types <- unique(adv$X)
  medication_types <- c(unique(comed$X), unique(reg$X))

  dt <- rbindlist(list(comed, adv, reg, out), use.names = TRUE)
  setorder(dt, id, time)

  terminal_times <- find_terminal(dt, outcomes)
  dt <- merge(dt, terminal_times, by = "id", all.x = TRUE, suffixes = c("", "_terminal"))
  dt <- dt[time <= time_terminal] # Keep only observations before the terminal time
  dt <- dt[!(time == time_terminal & !(X %in% outcomes))] ## Remove event if not terminal
  dt[, time_terminal := NULL] # Remove the terminal time column as it's no longer needed
  dt <- dt[id %in% id_regimen] # Keep only ids in the regimen

  for (event in adverse_event_types) {
    dt[, (event) := cumsum(X == event), by = id]
  }

  message("Following medication types found: ", paste(medication_types, collapse = ", "))
  for (med in medication_types) {
    message("Processing medication: ", med)
    dt <- dt[, jump_process_format_fast(copy(.SD), med), by = id]
  }
  dt[, val := NULL] # Remove the val column as it's no longer needed
  fix_duplicates(dt, treat_name) # Fix duplicates in the data
}
