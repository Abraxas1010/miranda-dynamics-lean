// Billiard ball simulation demonstrating pure observational information loss

let canvas, ctx;
let balls = [];
let precision = 3;
let animationTime = 0;

const TABLE = {
  width: 380,
  height: 180,
  padding: 10
};

class Ball {
  constructor(x, y, vx, vy, radius = 12, color = '#ffffff') {
    this.x = x;
    this.y = y;
    this.vx = vx;
    this.vy = vy;
    this.radius = radius;
    this.color = color;
    this.trail = [];
  }

  get truePosition() {
    return { x: this.x, y: this.y };
  }

  get observedPosition() {
    const factor = Math.pow(10, precision);
    return {
      x: Math.round(this.x * factor) / factor,
      y: Math.round(this.y * factor) / factor
    };
  }

  get informationGap() {
    const obs = this.observedPosition;
    return Math.sqrt(
      Math.pow(this.x - obs.x, 2) +
      Math.pow(this.y - obs.y, 2)
    );
  }

  update(dt) {
    // Store trail
    this.trail.push({ x: this.x, y: this.y });
    if (this.trail.length > 50) this.trail.shift();

    // Update position
    this.x += this.vx * dt;
    this.y += this.vy * dt;

    // Wall collisions (elastic, reversible)
    const minX = TABLE.padding + this.radius;
    const maxX = TABLE.width - TABLE.padding - this.radius;
    const minY = TABLE.padding + this.radius;
    const maxY = TABLE.height - TABLE.padding - this.radius;

    if (this.x <= minX || this.x >= maxX) {
      this.vx = -this.vx;
      this.x = Math.max(minX, Math.min(maxX, this.x));
    }
    if (this.y <= minY || this.y >= maxY) {
      this.vy = -this.vy;
      this.y = Math.max(minY, Math.min(maxY, this.y));
    }
  }

  draw(ctx) {
    // Draw trail
    ctx.beginPath();
    this.trail.forEach((pos, i) => {
      const alpha = i / this.trail.length * 0.3;
      ctx.strokeStyle = `rgba(255, 255, 255, ${alpha})`;
      if (i === 0) {
        ctx.moveTo(pos.x, pos.y);
      } else {
        ctx.lineTo(pos.x, pos.y);
      }
    });
    ctx.stroke();

    // Draw true position (small dot)
    ctx.beginPath();
    ctx.arc(this.x, this.y, this.radius, 0, Math.PI * 2);
    ctx.fillStyle = this.color;
    ctx.fill();
    ctx.strokeStyle = '#ffffff';
    ctx.lineWidth = 2;
    ctx.stroke();

    // Draw observed position (larger ring)
    const obs = this.observedPosition;
    ctx.beginPath();
    ctx.arc(obs.x, obs.y, this.radius + 4, 0, Math.PI * 2);
    ctx.strokeStyle = '#ffaa00';
    ctx.lineWidth = 2;
    ctx.setLineDash([4, 4]);
    ctx.stroke();
    ctx.setLineDash([]);

    // Draw gap line
    if (this.informationGap > 0.1) {
      ctx.beginPath();
      ctx.moveTo(this.x, this.y);
      ctx.lineTo(obs.x, obs.y);
      ctx.strokeStyle = '#ff4444';
      ctx.lineWidth = 1;
      ctx.stroke();
    }
  }
}

export function initBilliard(canvasId) {
  canvas = document.getElementById(canvasId);
  ctx = canvas.getContext('2d');

  // Set canvas size
  canvas.width = TABLE.width;
  canvas.height = TABLE.height;

  // Create balls
  resetBalls();
}

function resetBalls() {
  balls = [
    new Ball(100, 90, 80, 45, 12, '#00ff88'),
    new Ball(280, 60, -60, 70, 12, '#4488ff'),
    new Ball(200, 140, 50, -50, 12, '#ff4488')
  ];
}

export function setBilliardPrecision(p) {
  precision = p;
  updateStatsDisplay();
}

export function updateBilliard(dt) {
  if (dt > 0.1) dt = 0.016; // Cap delta time

  animationTime += dt;

  // Update balls
  balls.forEach(ball => ball.update(dt * 60)); // Scale for visible motion

  // Check ball-ball collisions
  for (let i = 0; i < balls.length; i++) {
    for (let j = i + 1; j < balls.length; j++) {
      handleBallCollision(balls[i], balls[j]);
    }
  }

  // Draw
  draw();
  updateStatsDisplay();
}

function handleBallCollision(ball1, ball2) {
  const dx = ball2.x - ball1.x;
  const dy = ball2.y - ball1.y;
  const distance = Math.sqrt(dx * dx + dy * dy);

  if (distance < ball1.radius + ball2.radius) {
    // Elastic collision (perfectly reversible)
    const nx = dx / distance;
    const ny = dy / distance;

    const dvx = ball1.vx - ball2.vx;
    const dvy = ball1.vy - ball2.vy;
    const dvn = dvx * nx + dvy * ny;

    if (dvn > 0) {
      ball1.vx -= dvn * nx;
      ball1.vy -= dvn * ny;
      ball2.vx += dvn * nx;
      ball2.vy += dvn * ny;

      // Separate balls
      const overlap = (ball1.radius + ball2.radius - distance) / 2;
      ball1.x -= overlap * nx;
      ball1.y -= overlap * ny;
      ball2.x += overlap * nx;
      ball2.y += overlap * ny;
    }
  }
}

function draw() {
  // Clear canvas
  ctx.fillStyle = '#1a1a2e';
  ctx.fillRect(0, 0, TABLE.width, TABLE.height);

  // Draw table border
  ctx.strokeStyle = '#4a4a6a';
  ctx.lineWidth = 3;
  ctx.strokeRect(TABLE.padding, TABLE.padding,
                 TABLE.width - 2 * TABLE.padding,
                 TABLE.height - 2 * TABLE.padding);

  // Draw precision grid (subtle)
  ctx.strokeStyle = 'rgba(100, 100, 150, 0.1)';
  ctx.lineWidth = 1;
  const gridSize = Math.pow(10, 2 - precision) * 100;
  if (gridSize > 5) {
    for (let x = 0; x < TABLE.width; x += gridSize) {
      ctx.beginPath();
      ctx.moveTo(x, 0);
      ctx.lineTo(x, TABLE.height);
      ctx.stroke();
    }
    for (let y = 0; y < TABLE.height; y += gridSize) {
      ctx.beginPath();
      ctx.moveTo(0, y);
      ctx.lineTo(TABLE.width, y);
      ctx.stroke();
    }
  }

  // Draw balls
  balls.forEach(ball => ball.draw(ctx));

  // Draw legend
  ctx.fillStyle = '#888';
  ctx.font = '10px sans-serif';
  ctx.fillText('True position (solid)', 10, TABLE.height - 25);
  ctx.fillText('Observed position j (dashed)', 10, TABLE.height - 12);
}

function updateStatsDisplay() {
  const ball = balls[0]; // Show stats for first ball

  const truePos = document.getElementById('true-position');
  const obsPos = document.getElementById('observed-position');
  const gapEl = document.getElementById('billiard-gap');

  if (truePos) {
    truePos.textContent = `(${ball.x.toFixed(6)}, ${ball.y.toFixed(6)})`;
  }

  if (obsPos) {
    const obs = ball.observedPosition;
    obsPos.textContent = `(${obs.x.toFixed(precision)}, ${obs.y.toFixed(precision)})`;
  }

  if (gapEl) {
    gapEl.textContent = ball.informationGap.toFixed(6);
    gapEl.style.color = ball.informationGap > 0.01 ? '#ffaa00' : '#00ff88';
  }
}
