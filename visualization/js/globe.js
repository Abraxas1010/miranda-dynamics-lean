// Globe visualization using CesiumJS

let stationEntities = {};
let waveFrontEntities = { pWave: null, sWave: null };
let epicenterEntity = null;
let viewerInitialized = false;

export async function initGlobe(containerId) {
  try {
    // Completely disable Cesium ion to avoid 401 errors
    Cesium.Ion.defaultAccessToken = '';

    // Suppress ion-related errors
    const originalError = console.error;
    console.error = function(...args) {
      if (args[0] && typeof args[0] === 'object' && args[0].statusCode === 401) {
        return; // Suppress 401 errors from ion
      }
      originalError.apply(console, args);
    };

    // Create OpenStreetMap imagery provider first
    const osmProvider = new Cesium.OpenStreetMapImageryProvider({
      url: 'https://tile.openstreetmap.org/'
    });

    // Create viewer with explicit non-ion providers
    const viewer = new Cesium.Viewer(containerId, {
      imageryProvider: osmProvider,           // Use OSM directly
      terrainProvider: new Cesium.EllipsoidTerrainProvider(), // No terrain (offline)
      baseLayerPicker: false,
      animation: false,
      timeline: false,
      geocoder: false,
      homeButton: false,
      sceneModePicker: false,
      navigationHelpButton: false,
      fullscreenButton: false,
      infoBox: false,
      selectionIndicator: false,
      creditContainer: document.createElement('div'),
      skyBox: false,
      skyAtmosphere: false,
      shadows: false,
      terrainShadows: Cesium.ShadowMode.DISABLED,
      requestRenderMode: false,  // Continuous rendering for animation
      contextOptions: {
        webgl: {
          alpha: false,
          antialias: true,
          preserveDrawingBuffer: true,
          powerPreference: 'high-performance'
        }
      }
    });

    // Set initial camera position - fixed view looking at Pacific
    viewer.camera.setView({
      destination: Cesium.Cartesian3.fromDegrees(150, -10, 25000000),
      orientation: {
        heading: 0,
        pitch: -Cesium.Math.PI_OVER_TWO,
        roll: 0
      }
    });

    // Disable automatic camera behaviors
    viewer.scene.screenSpaceCameraController.enableRotate = true;
    viewer.scene.screenSpaceCameraController.enableTranslate = false;
    viewer.scene.screenSpaceCameraController.enableZoom = true;
    viewer.scene.screenSpaceCameraController.enableTilt = false;
    viewer.scene.screenSpaceCameraController.enableLook = false;
    viewer.scene.screenSpaceCameraController.minimumZoomDistance = 1000000;  // Don't zoom too close
    viewer.scene.screenSpaceCameraController.maximumZoomDistance = 50000000; // Don't zoom too far

    // Disable auto-tracking behaviors
    viewer.trackedEntity = undefined;
    viewer.scene.globe.depthTestAgainstTerrain = false;

    // Dark background
    viewer.scene.backgroundColor = Cesium.Color.fromCssColorString('#0a0a1a');
    viewer.scene.globe.baseColor = Cesium.Color.fromCssColorString('#1a1a3a');

    // Disable lighting effects that could cause visual changes
    viewer.scene.globe.enableLighting = false;

    // Enable picking for station clicks
    viewer.screenSpaceEventHandler.setInputAction((click) => {
      const pickedObject = viewer.scene.pick(click.position);
      if (Cesium.defined(pickedObject) && pickedObject.id && pickedObject.id.stationCode) {
        window.showStationDetails(pickedObject.id.stationCode);
      }
    }, Cesium.ScreenSpaceEventType.LEFT_CLICK);

    viewerInitialized = true;
    console.log('Globe initialized successfully');
    return viewer;

  } catch (error) {
    console.error('Failed to initialize globe:', error);
    viewerInitialized = false;
    return null;
  }
}

export function addStationMarkers(viewer, stations, results, event) {
  if (!viewer || !viewerInitialized) {
    console.warn('Viewer not initialized, skipping station markers');
    return;
  }

  try {
    // Remove existing entities
    Object.values(stationEntities).forEach(entity => {
      try { viewer.entities.remove(entity); } catch(e) {}
    });
    if (epicenterEntity) {
      try { viewer.entities.remove(epicenterEntity); } catch(e) {}
    }
    stationEntities = {};
    epicenterEntity = null;

    console.log('Adding epicenter at:', event.longitude, event.latitude);

    // Add epicenter (earthquake location)
    epicenterEntity = viewer.entities.add({
      position: Cesium.Cartesian3.fromDegrees(event.longitude, event.latitude),
      point: {
        pixelSize: 24,
        color: Cesium.Color.RED,
        outlineColor: Cesium.Color.WHITE,
        outlineWidth: 3
      },
      label: {
        text: `M${event.magnitude} ${event.name}`,
        font: 'bold 14px sans-serif',
        fillColor: Cesium.Color.WHITE,
        outlineColor: Cesium.Color.BLACK,
        outlineWidth: 2,
        style: Cesium.LabelStyle.FILL_AND_OUTLINE,
        verticalOrigin: Cesium.VerticalOrigin.BOTTOM,
        pixelOffset: new Cesium.Cartesian2(0, -30)
      }
    });

    // Add station markers
    let stationCount = 0;
    stations.forEach(station => {
      const result = results.find(r => r.station === station.code);
      if (!result) return;

      const color = getStationColor(result, false);

      const entity = viewer.entities.add({
        position: Cesium.Cartesian3.fromDegrees(station.longitude, station.latitude),
        point: {
          pixelSize: 14,
          color: color,
          outlineColor: Cesium.Color.WHITE,
          outlineWidth: 2
        },
        label: {
          text: station.code.split('.')[1],
          font: '12px sans-serif',
          fillColor: Cesium.Color.WHITE,
          outlineColor: Cesium.Color.BLACK,
          outlineWidth: 1,
          style: Cesium.LabelStyle.FILL_AND_OUTLINE,
          verticalOrigin: Cesium.VerticalOrigin.TOP,
          pixelOffset: new Cesium.Cartesian2(0, 18)
        },
        stationCode: station.code,
        result: result
      });

      stationEntities[station.code] = entity;
      stationCount++;
    });

    console.log(`Added ${stationCount} station markers`);

    // Request render update
    viewer.scene.requestRender();

  } catch (error) {
    console.error('Error adding station markers:', error);
  }
}

function getStationColor(result, hasArrived) {
  if (!hasArrived) {
    return Cesium.Color.GRAY.withAlpha(0.6);
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
  if (!viewer || !viewerInitialized) return;

  try {
    // Remove existing wave fronts
    if (waveFrontEntities.pWave) {
      try { viewer.entities.remove(waveFrontEntities.pWave); } catch(e) {}
      waveFrontEntities.pWave = null;
    }
    if (waveFrontEntities.sWave) {
      try { viewer.entities.remove(waveFrontEntities.sWave); } catch(e) {}
      waveFrontEntities.sWave = null;
    }

    if (currentTime <= 0) {
      viewer.scene.requestRender();
      return;
    }

    // Calculate wave front radii (in meters)
    const pWaveRadius = currentTime * waveVelocity.p_wave_km_s * 1000;
    const sWaveRadius = currentTime * waveVelocity.s_wave_km_s * 1000;

    // P-wave front (green) - faster wave
    if (pWaveRadius > 0 && pWaveRadius < 20000000) {
      waveFrontEntities.pWave = viewer.entities.add({
        position: Cesium.Cartesian3.fromDegrees(event.longitude, event.latitude),
        ellipse: {
          semiMajorAxis: pWaveRadius,
          semiMinorAxis: pWaveRadius,
          material: Cesium.Color.fromCssColorString('#00ff88').withAlpha(0.1),
          outline: true,
          outlineColor: Cesium.Color.fromCssColorString('#00ff88').withAlpha(0.9),
          outlineWidth: 3,
          height: 0
        }
      });
    }

    // S-wave front (red) - slower wave
    if (sWaveRadius > 0 && sWaveRadius < 20000000) {
      waveFrontEntities.sWave = viewer.entities.add({
        position: Cesium.Cartesian3.fromDegrees(event.longitude, event.latitude),
        ellipse: {
          semiMajorAxis: sWaveRadius,
          semiMinorAxis: sWaveRadius,
          material: Cesium.Color.fromCssColorString('#ff4444').withAlpha(0.1),
          outline: true,
          outlineColor: Cesium.Color.fromCssColorString('#ff4444').withAlpha(0.7),
          outlineWidth: 2,
          height: 0
        }
      });
    }

    // Update station colors based on wave arrival
    Object.entries(stationEntities).forEach(([code, entity]) => {
      const result = entity.result;
      if (!result) return;

      const hasArrived = currentTime >= result.predicted_arrival_s;
      const color = getStationColor(result, hasArrived);

      entity.point.color = color;
      entity.point.pixelSize = hasArrived ? 18 : 14;

      // Pulsing effect for Heyting gap station
      if (hasArrived && result.is_heyting_gap) {
        const pulseScale = 1 + 0.3 * Math.sin(Date.now() / 200);
        entity.point.pixelSize = 18 * pulseScale;
      }
    });

    // Request render update
    viewer.scene.requestRender();

  } catch (error) {
    console.error('Error updating wave fronts:', error);
  }
}

export function highlightStation(viewer, stationCode) {
  if (!viewer || !viewerInitialized) return;

  // Reset all stations
  Object.values(stationEntities).forEach(entity => {
    if (entity.point) entity.point.outlineWidth = 2;
  });

  // Highlight selected station
  if (stationEntities[stationCode] && stationEntities[stationCode].point) {
    stationEntities[stationCode].point.outlineWidth = 4;
  }

  viewer.scene.requestRender();
}
