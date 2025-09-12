### get_baseline.R ---
#----------------------------------------------------------------------
## author:
## created: aug 15 2025 (11:53)
## Version:
## last-updated: sep  2 2025 (15:00) 
##     Update #: 12
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

get_baseline <- function(sexage, dt_index) {
  sexage <- merge(sexage, dt_index, by = "pnr")
  sexage[, age := as.numeric(difftime(index_date, foed_dag, unit = "weeks")) / 52.25]
  sexage[, agegroup := Publish::acut(age, breaks = c(-Inf, seq(45, 85, by = 5), Inf), right = FALSE, format = "%l-%u", format.low = "below %u", format.high = "above %l")]
  sexage[, c("foed_dag", "index_date", "end_date", "age") := NULL]
  sexage
}

#----------------------------------------------------------------------
### get_baseline.R ends here
