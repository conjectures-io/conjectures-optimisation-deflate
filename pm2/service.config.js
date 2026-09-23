// The validator under PM2: four processes, each doing one thing.
//
//   submission-api   serves /submit, /submissions, /leaderboard
//   gate-worker      drains the queue through the six-stage gate
//   chain-watcher    streams subnet registrations into the store
//   weight-setter    scores the round and sets weights, once an epoch
//
//   pm2 start pm2/service.config.js                      all four
//   pm2 start pm2/service.config.js --only miniz-oxide-gate-worker    one machine's gate only
//
// They are separate processes on purpose. The gate is a ~45 minute subprocess per
// submission; inside the API it pinned uvicorn to a single worker and took the API down
// whenever it died. The two chain workers need the bittensor SDK (./setup.sh --chain)
// and nothing else does.
//
// Postgres is not here: it comes up with `just db-up` (or a managed instance), and the
// schema with `just db-migrate`, before any of these start.
const fs = require("fs");
const path = require("path");
const root = path.join(__dirname, "..");

// .env, as written by setup.sh: KEY=value lines, '#' comments.
const env = {};
const dotenv = path.join(root, ".env");
if (fs.existsSync(dotenv)) {
  for (const line of fs.readFileSync(dotenv, "utf8").split("\n")) {
    const m = line.match(/^\s*([A-Z_]+)=(.*)$/);
    if (m) env[m[1]] = m[2].trim();
  }
}

// Explicit shell/just environment overrides the values loaded from .env.
Object.assign(env, process.env);

const python = path.join(root, ".venv/bin/python");
const cwd = path.join(root, "validator");

module.exports = {
  apps: [
    {
      name: "miniz-oxide-submission-api",
      cwd,
      script: python,
      interpreter: "none",
      args: "-m service.api",
      env,
      autorestart: true,
      max_restarts: 10,
    },
    {
      name: "miniz-oxide-gate-worker",
      cwd,
      script: python,
      interpreter: "none",
      args: "-m service.worker",
      // Each worker needs its own id: it is what the submissions table records as the
      // holder of a claim, and what tells two workers on one box apart.
      env: { ...env, SERVICE_WORKER_ID: `${require("os").hostname()}-pm2` },
      autorestart: true,
      max_restarts: 10,
      // The gate is a long subprocess; give it time to finish the one in flight.
      kill_timeout: 30000,
    },
    {
      // Without this, no hotkey has a registration and so nobody can submit at all.
      name: "miniz-oxide-chain-watcher",
      cwd,
      script: python,
      interpreter: "none",
      args: "-m workers.chain_watcher",
      env,
      autorestart: true,
      max_restarts: 10,
    },
    {
      name: "miniz-oxide-weight-setter",
      cwd,
      script: python,
      interpreter: "none",
      args: "-m workers.weight_setter",
      env,
      autorestart: true,
      max_restarts: 10,
    },
  ],
};
