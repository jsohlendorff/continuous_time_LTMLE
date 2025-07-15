### combine_hba_regimen.R ---
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jul 10 2025 (10:20)
## Version:
## Last-Updated: Jul 10 2025 (11:10)
##           By: Johan Sebastian Ohlendorff
##     Update #: 18
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:
combine_hba_regimen <- function(regime_cleaned, hba_cleaned, id_regimen_lira) {
  ## regime_cleaned <- tar_read(regime_cleaned)
  ## hba_cleaned <- tar_read(hba_cleaned)

  hba_cleaned[, X := "hba"]
  hba_cleaned[, val := NA_real_]
  res <- rbind(regime_cleaned, hba_cleaned)
  setorder(res, id, time, -X) # X order: placebo and lira, then hba
  res[, val := as.numeric(as.character(val))]
  res[, val := nafill(val, type = "locf"), by = "id"]
  res <- res[val == 0 | X == "hba"] ## Now consists of deviation times and hba measurements
  res[id %in% id_regimen_lira, X := "lira"] # Set X to lira for ids in id_regimen_lira
  res[(!id %in% id_regimen_lira), X := "placebo"] # Set X to placebo for ids not in id_regimen_lira
  res
}


######################################################################
### combine_hba_regimen.R ends here
