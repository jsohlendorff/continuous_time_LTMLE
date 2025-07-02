library(ggplot2)
library(targets)
library(purrr)
library(knitr)
library(dplyr)
setwd("~/phd/continuous_time_LTMLE/simulation_study")

## extract names of targets starting with "boxplot_"
target_names_plots <- tar_manifest() |>
  select(name) |> 
  filter(grepl("^boxplot_", name))

for (name in target_names_plots$name) {
  message("Saving plot for: ", name)
  p <- tar_read_raw(name)
  ggplot2::ggsave(filename = paste0("plots/",name, ".svg"), device="svg", plot = p[[1]], width = 10, height = 8)
  ggplot2::ggsave(filename = paste0("plots/se_", name, ".svg"), device="svg", plot = p[[2]], width = 10, height = 8)
}

p <- tar_read_raw("boxplot_results_censored")
ggplot2::ggsave(filename = paste0("plots/boxplot_results_censored_ice_ipcw.svg"), device="svg", plot = p[[3]], width = 10, height = 8)

target_names_tables <- tar_manifest() |>
  select(name) |> 
  filter(grepl("^results_table", name))

if (!dir.exists("tables")) {
  dir.create("tables")
}

for (name in target_names_tables$name) {
  message("Saving table for: ", name)
  df <- tar_read_raw(name)
  ## round to 3 significant digits
  df <- df |>
    mutate(across(where(is.numeric), ~ signif(., 3)))
  #res_table<-knitr::kable(df, format = "simple") #pipe
  ## save in a file; create necessary file
  file_name <- paste0("tables/", name, ".csv")
  if (!file.exists(file_name)) {
    file.create(file_name)
  }
  ## remove headers,
  write.csv(df, file = file_name, row.names = FALSE, na = "")
  #writeLines(res_table, file_name)
}