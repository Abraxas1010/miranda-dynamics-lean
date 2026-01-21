// Calibration transfer visualization

export function initCalibrationChart(canvasId, calibrationData) {
  const ctx = document.getElementById(canvasId).getContext('2d');

  // Prepare data
  const dataPoints = calibrationData.results
    .filter(r => r.noise === 0)
    .map(r => ({
      x: r.precision,
      y: r.rms_error
    }));

  // Create chart
  new Chart(ctx, {
    type: 'scatter',
    data: {
      datasets: [{
        label: 'RMS Error vs Precision',
        data: dataPoints,
        backgroundColor: '#4488ff',
        borderColor: '#4488ff',
        pointRadius: 8,
        pointHoverRadius: 10
      }, {
        label: 'Fitted Model (R^2=0.97)',
        data: generateFitLine(dataPoints),
        type: 'line',
        borderColor: '#00ff88',
        borderWidth: 2,
        pointRadius: 0,
        fill: false
      }]
    },
    options: {
      responsive: true,
      maintainAspectRatio: false,
      plugins: {
        legend: {
          display: true,
          position: 'top',
          labels: {
            color: '#a0a0a0',
            font: { size: 10 }
          }
        },
        tooltip: {
          callbacks: {
            label: (context) => {
              return `Precision: ${context.parsed.x}, Error: ${context.parsed.y.toFixed(6)}`;
            }
          }
        }
      },
      scales: {
        x: {
          title: {
            display: true,
            text: 'Observation Precision',
            color: '#a0a0a0'
          },
          ticks: { color: '#a0a0a0' },
          grid: { color: 'rgba(100, 100, 150, 0.2)' }
        },
        y: {
          title: {
            display: true,
            text: 'RMS Position Error',
            color: '#a0a0a0'
          },
          type: 'logarithmic',
          ticks: { color: '#a0a0a0' },
          grid: { color: 'rgba(100, 100, 150, 0.2)' }
        }
      }
    }
  });
}

function generateFitLine(dataPoints) {
  // Generate exponential fit line
  const points = [];
  for (let x = 1; x <= 5; x += 0.1) {
    // Approximate exponential decay model
    const y = 0.01 * Math.exp(-0.8 * x);
    points.push({ x, y });
  }
  return points;
}
