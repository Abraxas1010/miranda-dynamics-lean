import { VALIDATION_DATA, greatCircleDistance, WAVE_VELOCITY } from './data.js';
import { initGlobe, updateWaveFronts, addStationMarkers, highlightStation } from './globe.js';
import { initBilliard, updateBilliard, setBilliardPrecision } from './billiard.js';
import { initCalibrationChart } from './calibration.js';
import { showHeytingGapModal, hideHeytingGapModal } from './heyting-gap.js';

// Application State
const state = {
  currentEventId: 'us7000rqjy',
  currentTime: 0,        // seconds since earthquake
  isPlaying: false,
  playbackSpeed: 5,
  maxTime: 1200,         // 20 minutes max
  gapModalShown: false,  // Only show once per session
  viewer: null           // Cesium viewer
};

// DOM Elements
const eventSelect = document.getElementById('event-select');
const playPauseBtn = document.getElementById('play-pause-btn');
const timeSlider = document.getElementById('time-slider');
const timeDisplay = document.getElementById('time-display');
const speedSelect = document.getElementById('speed-select');
const precisionSlider = document.getElementById('precision-slider');
const precisionDisplay = document.getElementById('precision-display');

// Initialize Application
async function init() {
  console.log('Initializing Miranda Dynamics Visualization...');

  // Initialize Cesium globe
  state.viewer = await initGlobe('cesium-container');

  // Initialize billiard simulation
  initBilliard('billiard-canvas');

  // Initialize calibration chart
  initCalibrationChart('calibration-chart', VALIDATION_DATA.billiard_calibration);

  // Load initial event
  loadEvent(state.currentEventId);

  // Setup event listeners
  setupEventListeners();

  // Start animation loop
  requestAnimationFrame(animationLoop);

  console.log('Initialization complete.');
}

function loadEvent(eventId) {
  state.currentEventId = eventId;
  state.currentTime = 0;
  state.gapModalShown = false;

  const event = VALIDATION_DATA.events.find(e => e.id === eventId);
  const results = VALIDATION_DATA.results.filter(r => r.event_id === eventId);

  // Update globe
  addStationMarkers(state.viewer, VALIDATION_DATA.stations, results, event);

  // Reset timeline
  timeSlider.value = 0;
  updateTimeDisplay(0);

  // Reset station details
  document.getElementById('details-content').style.display = 'none';
  document.querySelector('.station-details .hint').style.display = 'block';
}

function setupEventListeners() {
  // Event selector
  eventSelect.addEventListener('change', (e) => {
    loadEvent(e.target.value);
  });

  // Play/Pause button
  playPauseBtn.addEventListener('click', () => {
    state.isPlaying = !state.isPlaying;
    playPauseBtn.textContent = state.isPlaying ? 'Pause' : 'Play';
    playPauseBtn.classList.toggle('playing', state.isPlaying);
  });

  // Time slider
  timeSlider.addEventListener('input', (e) => {
    state.currentTime = parseFloat(e.target.value);
    updateTimeDisplay(state.currentTime);
  });

  // Speed selector
  speedSelect.addEventListener('change', (e) => {
    state.playbackSpeed = parseFloat(e.target.value);
  });

  // Precision slider
  precisionSlider.addEventListener('input', (e) => {
    const precision = parseInt(e.target.value);
    precisionDisplay.textContent = `${precision} decimal places`;
    setBilliardPrecision(precision);
  });

  // Modal close buttons
  document.querySelectorAll('.modal-close, #close-gap-modal').forEach(btn => {
    btn.addEventListener('click', () => {
      hideHeytingGapModal();
    });
  });

  // Close modal on background click
  document.querySelectorAll('.modal').forEach(modal => {
    modal.addEventListener('click', (e) => {
      if (e.target === modal) {
        modal.classList.add('hidden');
      }
    });
  });
}

function updateTimeDisplay(time) {
  const minutes = Math.floor(time / 60);
  const seconds = Math.floor(time % 60);
  timeDisplay.textContent = `T+${minutes}:${seconds.toString().padStart(2, '0')}`;
}

let lastTimestamp = 0;

function animationLoop(timestamp) {
  const deltaTime = (timestamp - lastTimestamp) / 1000; // Convert to seconds
  lastTimestamp = timestamp;

  if (state.isPlaying && deltaTime < 1) { // Ignore large deltas (e.g., tab switch)
    state.currentTime += deltaTime * state.playbackSpeed;

    if (state.currentTime >= state.maxTime) {
      state.currentTime = state.maxTime;
      state.isPlaying = false;
      playPauseBtn.textContent = 'Play';
      playPauseBtn.classList.remove('playing');
    }

    timeSlider.value = state.currentTime;
    updateTimeDisplay(state.currentTime);
  }

  // Update visualizations
  const event = VALIDATION_DATA.events.find(e => e.id === state.currentEventId);
  const results = VALIDATION_DATA.results.filter(r => r.event_id === state.currentEventId);

  updateWaveFronts(state.viewer, event, state.currentTime, WAVE_VELOCITY);
  updateStationStates(results, state.currentTime);
  updateBilliard(deltaTime);

  // Check for Heyting gap trigger
  checkHeytingGapTrigger(results, state.currentTime);

  requestAnimationFrame(animationLoop);
}

function updateStationStates(results, currentTime) {
  results.forEach(result => {
    const station = VALIDATION_DATA.stations.find(s => s.code === result.station);
    if (!station) return;

    const predictedArrival = result.predicted_arrival_s;
    const hasArrived = currentTime >= predictedArrival;

    // Update station marker appearance based on arrival and category
    // This is handled in globe.js through Cesium entities
  });
}

function checkHeytingGapTrigger(results, currentTime) {
  if (state.gapModalShown) return;

  const gapResult = results.find(r => r.is_heyting_gap);
  if (!gapResult) return;

  // Trigger modal when wave "arrives" at the gap station
  if (currentTime >= gapResult.predicted_arrival_s && currentTime < gapResult.predicted_arrival_s + 2) {
    state.gapModalShown = true;
    state.isPlaying = false;
    playPauseBtn.textContent = 'Play';
    playPauseBtn.classList.remove('playing');

    showHeytingGapModal(gapResult);
  }
}

// Expose function for station clicks (called from globe.js)
window.showStationDetails = function(stationCode) {
  const result = VALIDATION_DATA.results.find(
    r => r.event_id === state.currentEventId && r.station === stationCode
  );
  const station = VALIDATION_DATA.stations.find(s => s.code === stationCode);

  if (!result || !station) return;

  document.querySelector('.station-details .hint').style.display = 'none';
  document.getElementById('details-content').style.display = 'block';

  document.getElementById('detail-station').textContent = `${station.code} (${station.name})`;
  document.getElementById('detail-category').textContent = result.category;
  document.getElementById('detail-category').style.color =
    result.category === 'j(P)=P' ? 'var(--accent-green)' : 'var(--accent-amber)';
  document.getElementById('detail-predicted').textContent = `${result.predicted_arrival_s.toFixed(1)}s`;
  document.getElementById('detail-observed').textContent =
    result.observed_arrival_s ? `${result.observed_arrival_s.toFixed(1)}s` : 'NOT DETECTED';
  document.getElementById('detail-error').textContent =
    result.error_s ? `${result.error_s.toFixed(3)}s` : 'N/A';
  document.getElementById('detail-snr').textContent = result.snr.toFixed(1);
  document.getElementById('detail-snr').style.color =
    result.snr < 3 ? 'var(--accent-red)' : 'var(--accent-green)';

  // Highlight station on globe
  highlightStation(state.viewer, stationCode);
};

// Start application
document.addEventListener('DOMContentLoaded', init);
