### get_outcome.R ---
#----------------------------------------------------------------------
## author:
## created: aug 15 2025 (11:57)
## Version:
## last-updated: sep  2 2025 (15:00) 
##     Update #: 47
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

get_outcome <- function(death, immiemi, dt_index, ids_hba1c_measured) {
  ## tar_load(dt_outcomes)
  # tar_load(death)
  # tar_load(immiemmi)
  # tar_load(dt_index)
  # tar_load(ids_hba1c_measured)
  ## resvarcular <- dt_outcomes$resvarcular
  ## resvarcular <- merge(resvarcular, dt_index, by = "pnr")
  ## resvarcular <- resvarcular[index_date <= inddto & inddto <= end_date & pnr %in% ids_hba1c_measured]
  ## resvarcular <- resvarcular[, .SD[1], by = "pnr"]

  ud <- unique(immiemi[indud_kode == "U", .(pnr, emi.date = haend_dato)])
  ud <- merge(ud, dt_index, by = "pnr")
  ud <- ud[index_date <= emi.date & emi.date <= end_date]
  ud <- ud[pnr %in% ids_hba1c_measured]
  ud <- ud[, .SD[1], by = "pnr"]
  death <- death[pnr %in% ids_hba1c_measured]

  outcome <- data.table(pnr = ids_hba1c_measured)
  outcome <- merge(outcome, death, by = "pnr", all = TRUE)
  outcome <- merge(outcome, ud[, c("pnr", "emi.date")], all = TRUE, by = "pnr")
  outcome <- merge(outcome, dt_index, by = "pnr")
  ## outcome <- merge(outcome, resvarcular[, c("inddto", "pnr")], by = "pnr", all = TRUE)
  outcome[, time := pmin(doddato, emi.date, end_date, na.rm = TRUE)]
  outcome[, event := "C"]
  outcome[doddato == time, event := "Y"] # "D"
  ## outcome[inddto == time, event := "Y"]
  outcome[, time := as.numeric(difftime(time, index_date, units = "days"))]
  outcome <- outcome[, c("pnr", "event", "time")]
  setnames(outcome, c("event"), c("X"))
  outcome$val <- NA
  outcome[time > 0]
}

#----------------------------------------------------------------------
### get_outcome.R ends here
