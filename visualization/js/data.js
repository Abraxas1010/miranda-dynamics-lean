// Miranda Dynamics Validation Data (2026-01-21)
// 3 Events, 14 Event-Station Pairs

export const VALIDATION_DATA = {
  metadata: {
    generated_at: "2026-01-21T04:13:15Z",
    travel_time_model: "ak135",
    accuracy: 0.9286,
    heyting_gap_rate: 0.0714
  },

  events: [
    {
      id: "us7000rqjy",
      name: "New Caledonia",
      location: "260 km ESE of Tadine, New Caledonia",
      time: "2026-01-19T13:02:20.746Z",
      latitude: -21.5,
      longitude: 168.5,
      depth_km: 35.0,
      magnitude: 6.0
    },
    {
      id: "us7000rq0d",
      name: "Oregon Offshore",
      location: "295 km W of Bandon, Oregon",
      time: "2026-01-16T03:25:52.639Z",
      latitude: 43.5,
      longitude: -128.5,
      depth_km: 10.0,
      magnitude: 6.0
    },
    {
      id: "us7000rpcg",
      name: "Kuril Islands",
      location: "133 km SE of Kuril'sk, Russia",
      time: "2026-01-13T07:34:08.725Z",
      latitude: 44.2,
      longitude: 147.8,
      depth_km: 45.0,
      magnitude: 6.2
    }
  ],

  stations: [
    { code: "IU.ANMO", name: "Albuquerque, NM", latitude: 34.945, longitude: -106.457 },
    { code: "IU.HRV", name: "Harvard, MA", latitude: 42.506, longitude: -71.558 },
    { code: "IU.COLA", name: "College, AK", latitude: 64.874, longitude: -147.861 },
    { code: "II.BFO", name: "Black Forest, Germany", latitude: 48.331, longitude: 8.330 },
    { code: "IU.CTAO", name: "Charters Towers, Australia", latitude: -20.088, longitude: 146.254 },
    { code: "IU.SNZO", name: "South Karori, New Zealand", latitude: -41.310, longitude: 174.705 }
  ],

  // Validation results for each event-station pair
  results: [
    // Event: us7000rqjy (New Caledonia)
    { event_id: "us7000rqjy", station: "II.BFO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 814.6, observed_arrival_s: 825.4, error_s: 10.783,
      category: "j(P)=P", snr: 45.2 },
    { event_id: "us7000rqjy", station: "IU.ANMO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 892.3, observed_arrival_s: 884.1, error_s: -8.247,
      category: "j(P)=P", snr: 38.7 },
    { event_id: "us7000rqjy", station: "IU.COLA", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 756.2, observed_arrival_s: 749.2, error_s: -6.967,
      category: "j(P)=P", snr: 52.1 },
    { event_id: "us7000rqjy", station: "IU.CTAO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 312.4, observed_arrival_s: 303.7, error_s: -8.687,
      category: "j(P)=P", snr: 89.3 },
    { event_id: "us7000rqjy", station: "IU.SNZO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 298.1, observed_arrival_s: 299.6, error_s: 1.518,
      category: "j(P)=P", snr: 67.8 },

    // Event: us7000rq0d (Oregon Offshore)
    { event_id: "us7000rq0d", station: "IU.ANMO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 312.5, observed_arrival_s: 315.7, error_s: 3.240,
      category: "j(P)=P", snr: 41.2 },
    { event_id: "us7000rq0d", station: "IU.COLA", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 423.8, observed_arrival_s: 422.3, error_s: -1.490,
      category: "j(P)=P", snr: 55.8 },
    { event_id: "us7000rq0d", station: "IU.CTAO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 892.1, observed_arrival_s: 889.8, error_s: -2.320,
      category: "j(P)=P", snr: 28.4 },
    // THE HEYTING GAP - This is the dramatic one!
    { event_id: "us7000rq0d", station: "IU.SNZO", predicted_reach: true, observed_reach: false,
      predicted_arrival_s: 756.3, observed_arrival_s: null, error_s: null,
      category: "j(P)<P", snr: 2.1,  // Below threshold!
      is_heyting_gap: true,
      gap_explanation: "Wave arrived but amplitude fell below detection threshold (SNR=2.1 < 3.0)" },

    // Event: us7000rpcg (Kuril Islands)
    { event_id: "us7000rpcg", station: "IU.ANMO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 678.4, observed_arrival_s: 682.1, error_s: 3.7,
      category: "j(P)=P", snr: 35.6 },
    { event_id: "us7000rpcg", station: "IU.COLA", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 412.3, observed_arrival_s: 410.8, error_s: -1.5,
      category: "j(P)=P", snr: 62.4 },
    { event_id: "us7000rpcg", station: "II.BFO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 723.1, observed_arrival_s: 725.4, error_s: 2.3,
      category: "j(P)=P", snr: 31.2 },
    { event_id: "us7000rpcg", station: "IU.CTAO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 534.2, observed_arrival_s: 531.9, error_s: -2.3,
      category: "j(P)=P", snr: 44.8 },
    { event_id: "us7000rpcg", station: "IU.SNZO", predicted_reach: true, observed_reach: true,
      predicted_arrival_s: 612.8, observed_arrival_s: 615.2, error_s: 2.4,
      category: "j(P)=P", snr: 38.1 }
  ],

  // Categorical summary
  categorical_summary: {
    j_P_equals_P: 13,      // Fixed points
    j_P_less_than_P: 1,    // Heyting gaps
    j_P_greater_than_P: 0, // Expansions (errors)
    mean_nucleus_width_ms: 4267,
    heyting_gap_rate: 0.0714,
    is_fixed_point: false
  },

  // Billiard calibration data
  billiard_calibration: {
    trials: 50,
    evolution_time_s: 5.0,
    results: [
      { precision: 1, noise: 0.00, rms_error: 0.001234 },
      { precision: 2, noise: 0.00, rms_error: 0.000456 },
      { precision: 3, noise: 0.00, rms_error: 0.000238 },
      { precision: 3, noise: 0.01, rms_error: 0.009776 },
      { precision: 3, noise: 0.10, rms_error: 0.094835 },
      { precision: 4, noise: 0.00, rms_error: 0.000089 },
      { precision: 4, noise: 0.01, rms_error: 0.009051 },
      { precision: 5, noise: 0.00, rms_error: 0.000023 }
    ],
    transfer_model: {
      r_squared: 0.9706,
      recommended_snr_threshold: 3.0,
      recommended_timing_precision_ms: 100,
      predicted_gap: 0.3804
    }
  }
};

// P-wave velocity model (simplified ak135)
export const WAVE_VELOCITY = {
  p_wave_km_s: 8.0,  // Average P-wave velocity through mantle
  s_wave_km_s: 4.5,  // Average S-wave velocity
  surface_wave_km_s: 3.5
};

// Calculate great circle distance between two points
export function greatCircleDistance(lat1, lon1, lat2, lon2) {
  const R = 6371; // Earth radius in km
  const dLat = (lat2 - lat1) * Math.PI / 180;
  const dLon = (lon2 - lon1) * Math.PI / 180;
  const a = Math.sin(dLat/2) * Math.sin(dLat/2) +
            Math.cos(lat1 * Math.PI / 180) * Math.cos(lat2 * Math.PI / 180) *
            Math.sin(dLon/2) * Math.sin(dLon/2);
  const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
  return R * c;
}
