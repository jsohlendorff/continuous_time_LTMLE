library(ggplot2)
library(targets)
library(purrr)
library(knitr)
library(dplyr)
setwd("~/phd/continuous_time_LTMLE/simulation_study")

if (!dir.exists("tables")) {
  dir.create("tables")
}
if (!dir.exists("plots")) {
  dir.create("plots")
}

## extract names of targets starting with "boxplot_"
target_names_plots <- tar_manifest() |>
  select(name) |>
  filter(grepl("^boxplot_", name))

for (name in target_names_plots$name) {
  message("Saving plot for: ", name)
  p <- tar_read_raw(name)
  ggplot2::ggsave(filename = paste0("plots/", name, ".pdf"), device=cairo_pdf, plot = p[[1]], width = 12, height = 10)
  ggplot2::ggsave(filename = paste0("plots/se_", name, ".pdf"), device=cairo_pdf, plot = p[[2]], width = 12, height = 10)
  if (length(p) >= 3) {
    ggplot2::ggsave(filename = paste0("plots/ice_ipcw_", name, ".pdf"), device=cairo_pdf, plot = p[[3]], width = 12, height = 10)
  }
  ## Use `pdf2svg` to convert PDF to SVG
  if (file.exists(paste0("plots/", name, ".pdf"))) {
    system(paste("pdf2svg", paste0("plots/", name, ".pdf"), paste0("plots/", name, ".svg")))
  }
  if (file.exists(paste0("plots/se_", name, ".pdf"))) {
    system(paste("pdf2svg", paste0("plots/se_", name, ".pdf"), paste0("plots/se_", name, ".svg")))
  }
  if (length(p) >= 3 && file.exists(paste0("plots/ice_ipcw_", name, ".pdf"))) {
    system(paste("pdf2svg", paste0("plots/ice_ipcw_", name, ".pdf"), paste0("plots/ice_ipcw_", name, ".svg")))
  }
}

target_names_tables <- tar_manifest() |>
  select(name) |>
  filter(grepl("table_", name))

for (name in target_names_tables$name) {
  message("Saving table for: ", name)
  df <- tar_read_raw(name)
  for (col in intersect(names(df),c("n","effect_A_on_L","effect_A_on_Y", "effect_L_on_Y", "effect_L_on_A", "baseline_rate_C"))) {
    if ("model_type" %in% names(df)) {
      df[!(type=="ICE-IPCW (Debiased)" & model_type == "Scaled Quasi-binmoial"), col] <- NA
    } else {
      df[!(type=="ICE-IPCW (Debiased)"), col] <- NA
    }
  }
  df <- df |>
    mutate(across(where(is.numeric), ~ signif(., 3)))
  file_name <- paste0("tables/", name, ".csv")
  if (!file.exists(file_name)) {
    file.create(file_name)
  }
  write.csv(df, file = file_name, row.names = FALSE, na = "")
}
