support_ice <- function(values, tau = 720, large_n = 10000, no_competing_events = TRUE) {
  res <- list()
  for (i in 1:nrow(values)) {
    data_continuous <- simulate_simple_continuous_time_data(n = large_n,
                                                            uncensored = TRUE,
                                                            no_competing_events = no_competing_events,
                                                            effects = vary_effect(
                                                              effect_A_on_Y = values$effect_A_on_Y[i],
                                                              effect_L_on_Y = values$effect_L_on_Y[i],
                                                              effect_L_on_A = values$effect_L_on_A[i],
                                                              effect_A_on_L = values$effect_A_on_L[i],
                                                              effect_age_on_Y = values$effect_age_on_Y[i],
                                                              effect_age_on_A = values$effect_age_on_A[i]
                                                            ))
    data_continuous$timevarying_data[, event_number := 1:.N, by = .(id)]
    at_risk_table <- data_continuous$timevarying_data[time < tau &
                                                        event %in% c("A", "L"), .N/large_n, by = "event_number"]
    at_risk_table[, c("effect_A_on_Y", "effect_L_on_Y", "effect_L_on_A", "effect_A_on_L",
                      "effect_age_on_Y", "effect_age_on_A") := values[i, ]]
    res[[i]] <- at_risk_table
    
  }
  rbindlist(res)
}