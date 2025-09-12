### get_regime.R ---
#----------------------------------------------------------------------
## author:
## created: aug 15 2025 (11:48)
## Version:
## last-updated: sep  2 2025 (15:00) 
##     Update #: 54
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

get_regime <- function(dt_sgl_dpp4, dt_lab, min_year = 2012, max_year = 2022) {
  regime <- dt_sgl_dpp4[drugdiab %in% c("sglt2_inhib", "dpp4_inhib")]
  regime <- regime[, end := NULL]

  ## Only look at years from 2012-2022
  regime <- regime[year(index_date) >= min_year & year(index_date) <= max_year]
  ids <- unique(regime[, pnr])
  dt_lab <- na.omit(dt_lab[class == "HBA1C" & pnr %in% ids])

  ## Contains start of study and end of study for each id
  dt_index <- unique(regime[, c("pnr", "index_date")])
  dt_index$end_date <- as.Date(paste0(max_year, "-12-31"))

  ## IDs having bought one perscription of dpp4 or sglt2 and having Hba1c measured before first purchase date
  ids_hba1c_measured <- merge(dt_lab, dt_index, by = "pnr")[, .(sum(start <= index_date)), by = "pnr"][V1 > 0, ]$pnr

  ## Count as treated if you haven't purchased the other medicine compared to the index date; val variable
  regime <- unique(regime[pnr %in% ids_hba1c_measured])
  regime[, dev := 0]
  regime[, val := 1]
  regime[drugdiab == "sglt2_inhib" & arm == "dpp4" | drugdiab == "dpp4_inhib" & arm == "sglt2", dev := 1]
  regime[, cum_dev := cumsum(dev), by = "pnr"]
  regime[cum_dev >= 1, val := 0]
  ## regime <- regime[cum_dev %in% c(0, 1)] ## discard purchase times after first deviation; weird?

  ## Time to days; cleanup
  regime[, time := as.numeric(difftime(start, index_date, units = "days"))]
  regime[, c("start", "drugdiab", "index_date", "dev", "cum_dev", "drugclass") := NULL]
  setnames(regime, c("arm"), c("X"))

  ## Can be two registrations for medicine if bought within same day i.e., both sglt2 and dpp4; in that case, count as unmedicated
  regime[, dup := duplicated(time) | duplicated(time, fromLast = TRUE), by = "pnr"]
  regime[dup == TRUE, val := 0] ## duplicate values correspond to purchasing both medicines
  regime[, dup := NULL]
  regime <- unique(regime)
  list(regime = regime, ids_hba1c_measured = ids_hba1c_measured, dt_index = dt_index)
}
#----------------------------------------------------------------------
### get_regime.R ends here
