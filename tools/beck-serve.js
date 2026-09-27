#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const http = require("node:http");
const crypto = require("node:crypto");

const { wasm } = require("./beck");

function createServer() {
  const binary = fs.readFileSync(wasm);
  const manifest = JSON.parse(fs.readFileSync(path.join(path.dirname(wasm), "manifest.json"), "utf8"));
  if (crypto.createHash("sha256").update(binary).digest("hex") !== manifest.sha256 ||
      binary.length !== manifest.byteLength || manifest.source !== "LeanExe.Examples.BeckExact.compute") {
    throw new Error("The Beck binary does not match its build manifest.");
  }
  const files = new Map([
    ["/program.wasm", ["application/wasm", binary]],
    ["/manifest.json", ["application/json", Buffer.from(JSON.stringify(manifest))]],
  ]);
  for (const [file, type] of [["index.html", "text/html"], ["style.css", "text/css"],
    ["app.mjs", "text/javascript"], ["worker.mjs", "text/javascript"], ["scenarios.mjs", "text/javascript"]]) {
    files.set(`/${file}`, [`${type}; charset=utf-8`, fs.readFileSync(path.join(__dirname, "beck-web", file))]);
  }
  files.set("/", files.get("/index.html"));
  return http.createServer((request, response) => {
    response.setHeader("Cache-Control", "no-store");
    response.setHeader("X-Content-Type-Options", "nosniff");
    response.setHeader("Content-Security-Policy", "default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; style-src 'self'; img-src 'self' data:; worker-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'none'");
    if (!["GET", "HEAD"].includes(request.method)) {
      response.writeHead(405, { Allow: "GET, HEAD" });
      response.end("Method not allowed");
      return;
    }
    let name;
    try { name = new URL(request.url, "http://localhost").pathname; }
    catch { response.writeHead(400); response.end("Invalid URL"); return; }
    const file = files.get(name);
    if (!file) { response.writeHead(404); response.end("Not found"); return; }
    response.writeHead(200, { "Content-Type": file[0], "Content-Length": file[1].length });
    response.end(request.method === "HEAD" ? undefined : file[1]);
  });
}

if (require.main === module) {
  try {
    const port = Number(process.argv[2] || 8091);
    if (process.argv.length > 3 || !Number.isInteger(port) || port < 1 || port > 65535) {
      throw new Error("usage: tools/beck-serve.js [PORT]");
    }
    const server = createServer();
    server.on("error", error => { process.stderr.write(`beck-serve: ${error.message}\n`); process.exitCode = 1; });
    server.listen(port, "0.0.0.0", () => process.stdout.write(`Beck demo: http://0.0.0.0:${port}\n`));
  } catch (error) {
    process.stderr.write(`beck-serve: ${error.message}\n`);
    process.exitCode = 1;
  }
}

module.exports = { createServer };
