// Globe visualization using CesiumJS

let stationEntities = {};
let waveFrontEntities = { pWave: null, sWave: null };
let epicenterEntity = null;

export async function initGlobe(containerId) {
  // Initialize Cesium viewer
  // Note: For production, get a free Cesium ion token at https://cesium.com/ion/
  // Replace the token below with your own
  Cesium.Ion.defaultAccessToken = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJqdGkiOiJlYWE1OWUxNy1mMWZiLTQzYjYtYTQ0OS1kMWFjYmFkNjc5YzciLCJpZCI6NTc1MzksImlhdCI6MTYyNzU1MjkzOH0.a1234567890';

  const viewer = new Cesium.Viewer(containerId, {
    terrainProvider: await Cesium.createWorldTerrainAsync(),
    animation: false,
    timeline: false,
    baseLayerPicker: false,
    geocoder: false,
    homeButton: false,
    sceneModePicker: false,
    navigationHelpButton: false,
    fullscreenButton: false,
    infoBox: false,
    selectionIndicator: false
  });

  // Set initial camera position
  viewer.camera.setView({
    destination: Cesium.Cartesian3.fromDegrees(150, -10, 20000000),
    orientation: {
      heading: 0,
      pitch: -Cesium.Math.PI_OVER_TWO,
      roll: 0
    }
  });

  // Dark atmosphere style
  viewer.scene.globe.enableLighting = false;
  viewer.scene.backgroundColor = Cesium.Color.fromCssColorString('#0a0a1a');

  // Enable picking
  viewer.screenSpaceEventHandler.setInputAction((click) => {
    const pickedObject = viewer.scene.pick(click.position);
    if (Cesium.defined(pickedObject) && pickedObject.id && pickedObject.id.stationCode) {
      window.showStationDetails(pickedObject.id.stationCode);
    }
  }, Cesium.ScreenSpaceEventType.LEFT_CLICK);

  return viewer;
}

export function addStationMarkers(viewer, stations, results, event) {
  // Remove existing entities
  Object.values(stationEntities).forEach(entity => viewer.entities.remove(entity));
  if (epicenterEntity) viewer.entities.remove(epicenterEntity);
  stationEntities = {};

  // Add epicenter
  epicenterEntity = viewer.entities.add({
    position: Cesium.Cartesian3.fromDegrees(event.longitude, event.latitude),
    point: {
      pixelSize: 20,
      color: Cesium.Color.RED,
      outlineColor: Cesium.Color.WHITE,
      outlineWidth: 3
    },
    label: {
      text: `M${event.magnitude} ${event.name}`,
      font: '14px sans-serif',
      fillColor: Cesium.Color.WHITE,
      outlineColor: Cesium.Color.BLACK,
      outlineWidth: 2,
      style: Cesium.LabelStyle.FILL_AND_OUTLINE,
      verticalOrigin: Cesium.VerticalOrigin.BOTTOM,
      pixelOffset: new Cesium.Cartesian2(0, -25)
    }
  });

  // Add station markers
  stations.forEach(station => {
    const result = results.find(r => r.station === station.code);
    if (!result) return;

    const color = getStationColor(result, false);

    const entity = viewer.entities.add({
      position: Cesium.Cartesian3.fromDegrees(station.longitude, station.latitude),
      point: {
        pixelSize: 12,
        color: color,
        outlineColor: Cesium.Color.WHITE,
        outlineWidth: 2
      },
      label: {
        text: station.code.split('.')[1],
        font: '11px sans-serif',
        fillColor: Cesium.Color.WHITE,
        outlineColor: Cesium.Color.BLACK,
        outlineWidth: 1,
        style: Cesium.LabelStyle.FILL_AND_OUTLINE,
        verticalOrigin: Cesium.VerticalOrigin.TOP,
        pixelOffset: new Cesium.Cartesian2(0, 15)
      },
      stationCode: station.code,
      result: result
    });

    stationEntities[station.code] = entity;
  });

  // Fly camera to event
  viewer.camera.flyTo({
    destination: Cesium.Cartesian3.fromDegrees(event.longitude, event.latitude, 15000000),
    duration: 2
  });
}

function getStationColor(result, hasArrived) {
  if (!hasArrived) {
    return Cesium.Color.GRAY.withAlpha(0.5);
  }

  if (result.category === 'j(P)=P') {
    return Cesium.Color.fromCssColorString('#00ff88');
  } else if (result.category === 'j(P)<P') {
    return Cesium.Color.fromCssColorString('#ffaa00');
  } else {
    return Cesium.Color.fromCssColorString('#ff4444');
  }
}

export function updateWaveFronts(viewer, event, currentTime, waveVelocity) {
  // Remove existing wave fronts
  if (waveFrontEntities.pWave) viewer.entities.remove(waveFrontEntities.pWave);
  if (waveFrontEntities.sWave) viewer.entities.remove(waveFrontEntities.sWave);

  if (currentTime <= 0) return;

  // Calculate wave front radii (in meters)
  const pWaveRadius = currentTime * waveVelocity.p_wave_km_s * 1000;
  const sWaveRadius = currentTime * waveVelocity.s_wave_km_s * 1000;

  // P-wave front (green)
  if (pWaveRadius > 0 && pWaveRadius < 20000000) {
    waveFrontEntities.pWave = viewer.entities.add({
      position: Cesium.Cartesian3.fromDegrees(event.longitude, event.latitude),
      ellipse: {
        semiMajorAxis: pWaveRadius,
        semiMinorAxis: pWaveRadius,
        material: Cesium.Color.fromCssColorString('#00ff88').withAlpha(0.0),
        outline: true,
        outlineColor: Cesium.Color.fromCssColorString('#00ff88').withAlpha(0.8),
        outlineWidth: 3
      }
    });
  }

  // S-wave front (red)
  if (sWaveRadius > 0 && sWaveRadius < 20000000) {
    waveFrontEntities.sWave = viewer.entities.add({
      position: Cesium.Cartesian3.fromDegrees(event.longitude, event.latitude),
      ellipse: {
        semiMajorAxis: sWaveRadius,
        semiMinorAxis: sWaveRadius,
        material: Cesium.Color.fromCssColorString('#ff4444').withAlpha(0.0),
        outline: true,
        outlineColor: Cesium.Color.fromCssColorString('#ff4444').withAlpha(0.6),
        outlineWidth: 2
      }
    });
  }

  // Update station colors based on arrival time
  Object.entries(stationEntities).forEach(([code, entity]) => {
    const result = entity.result;
    if (!result) return;

    const hasArrived = currentTime >= result.predicted_arrival_s;
    const color = getStationColor(result, hasArrived);

    entity.point.color = color;
    entity.point.pixelSize = hasArrived ? 16 : 12;

    // Add pulsing effect for Heyting gap station when arrived
    if (hasArrived && result.is_heyting_gap) {
      const pulseScale = 1 + 0.3 * Math.sin(Date.now() / 200);
      entity.point.pixelSize = 16 * pulseScale;
    }
  });
}

export function highlightStation(viewer, stationCode) {
  // Reset all stations
  Object.values(stationEntities).forEach(entity => {
    entity.point.outlineWidth = 2;
  });

  // Highlight selected station
  if (stationEntities[stationCode]) {
    stationEntities[stationCode].point.outlineWidth = 4;
  }
}
