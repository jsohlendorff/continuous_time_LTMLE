### get_hba1c.R ---
#----------------------------------------------------------------------
## author:
## created: aug 15 2025 (11:51)
## Version:
## last-updated: sep  2 2025 (15:00) 
##     Update #: 28
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

get_hba1c <- function(dt_lab, dt_index) {
  dt_lab <- merge(dt_lab, dt_index, by = "pnr")
  setnames(dt_index, c("index_date", "end_date"), c("study_start", "study_end"))
  dt_hba <- dt_lab[, c("pnr", "res", "start")]
  setnames(dt_hba, c("res", "start"), c("X", "start_date"))
  hba <- clean(dt_hba, dt_index, period = 1, type = "measurement", id_name = "pnr")
  hba <- hba[, .SD[.N], by = c("time", "pnr")] ## keep last measurement
  hba$X <- "hba1c"
  na.omit(hba)
}

#----------------------------------------------------------------------
### get_hba1c.R ends here
