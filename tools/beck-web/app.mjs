import { scenarios, invalidScenarios } from "./scenarios.mjs";

const $ = id => document.getElementById(id);
const categoryName = id => String.fromCharCode(65 + id);
let input;
let partitionWorker;
let validationWorker;

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function status(id, text, state = "") {
  $(id).textContent = text;
  $(id).dataset.state = state;
}

function execute(value, done) {
  const worker = new Worker("/worker.mjs", { type: "module" });
  const stop = () => { clearTimeout(timer); worker.terminate(); };
  const finish = result => { stop(); done(result); };
  const timer = setTimeout(() => finish({ ok: false, message: "The browser run exceeded 30 seconds." }), 30_000);
  worker.onmessage = event => finish(event.data);
  worker.onerror = event => {
    event.preventDefault();
    finish({ ok: false, message: event.message || "The browser worker failed." });
  };
  worker.postMessage(value);
  return stop;
}

function invalidate() {
  partitionWorker?.();
  partitionWorker = undefined;
  $("run").disabled = false;
  document.querySelector(".output").setAttribute("aria-busy", "false");
  $("results").hidden = true;
  status("status", "Memberships changed. Run the partition to see the new groups.");
}

function markCustom() {
  $("scenario").value = "custom";
  $("scenario-note").textContent = "Custom memberships. The bound uses the largest number of categories selected for any one job.";
  invalidate();
  updateSummary();
}

function updateSummary() {
  const count = input.jobs.reduce((sum, job) => sum + job.length, 0);
  $("input-summary").textContent = `${count} membership${count === 1 ? "" : "s"}`;
}

function renderInput() {
  $("job-count").value = input.jobs.length;
  $("category-count").value = input.categories;
  const table = element("table");
  const head = element("thead");
  const heading = element("tr");
  const jobHeading = element("th", "Job");
  jobHeading.scope = "col";
  heading.append(jobHeading);
  for (let category = 0; category < input.categories; category++) {
    const cell = element("th", categoryName(category));
    cell.scope = "col";
    heading.append(cell);
  }
  head.append(heading);
  const body = element("tbody");
  input.jobs.forEach((memberships, job) => {
    const row = element("tr");
    const label = element("th", `Job ${job + 1}`);
    label.scope = "row";
    row.append(label);
    for (let category = 0; category < input.categories; category++) {
      const cell = element("td", undefined, "membership-cell");
      const target = element("label");
      const box = document.createElement("input");
      box.type = "checkbox";
      box.checked = memberships.includes(category);
      box.setAttribute("aria-label", `Job ${job + 1}, category ${categoryName(category)}`);
      box.addEventListener("change", () => {
        input.jobs[job] = box.checked ? [...input.jobs[job], category].sort((a, b) => a - b) : input.jobs[job].filter(id => id !== category);
        markCustom();
      });
      target.append(box);
      cell.append(target);
      row.append(cell);
    }
    body.append(row);
  });
  table.append(head, body);
  $("membership-table").replaceChildren(table);
  if (input.jobs.length === 0) $("membership-table").append(element("p", "No jobs to assign.", "subtle"));
  else if (input.categories === 0) $("membership-table").append(element("p", "No categories. Every job has zero memberships.", "subtle"));
  updateSummary();
}

function showResult(result) {
  $("overlap").textContent = result.overlap;
  $("bound").textContent = result.bound;
  for (const [group, name] of ["a", "b"].entries()) {
    const jobs = result.assignments.flatMap((assignment, job) => assignment === group ? [job] : []);
    $(`group-${name}-count`).textContent = `${jobs.length} job${jobs.length === 1 ? "" : "s"}`;
    $(`group-${name}-jobs`).replaceChildren(...(jobs.length ? jobs.map(job => element("li", `Job ${job + 1}`, "job")) : [element("li", "No jobs", "empty")]));
  }
  const table = element("table");
  const heading = element("tr");
  for (const title of ["Category", "Total", "A", "B", "Difference"]) {
    const cell = element("th", title);
    cell.scope = "col";
    heading.append(cell);
  }
  const head = element("thead");
  head.append(heading);
  const body = element("tbody");
  for (const row of result.counts) {
    const tr = element("tr");
    const label = element("th", categoryName(row.category));
    label.scope = "row";
    tr.append(label, ...[row.total, ...row.groups].map(count => element("td", count)), element("td", `${row.difference} ≤ ${result.bound}`, "pass"));
    body.append(tr);
  }
  table.append(head, body);
  $("counts").replaceChildren(result.counts.length ? table : element("p", "No categories to count.", "subtle"));
  $("result-note").textContent = result.overlap === 0 ? "Zero overlap: all category differences are zero." : "The bound applies to each category. The total group sizes may differ.";
  $("results").hidden = false;
  status("status", result.counts.length ? "Every category is within the bound. Counts checked." : "All jobs assigned. There are no category constraints.", "passed");
}

function run() {
  invalidate();
  $("run").disabled = true;
  document.querySelector(".output").setAttribute("aria-busy", "true");
  status("status", "Running the verified WASM program.");
  partitionWorker = execute(input, result => {
    partitionWorker = undefined;
    $("run").disabled = false;
    document.querySelector(".output").setAttribute("aria-busy", "false");
    if (!result.ok) status("status", result.message, "error");
    else if (result.status !== 0) status("status", `WASM rejected the input (status ${result.status}).`, "error");
    else showResult(result);
  });
}

function loadScenario(id) {
  const scenario = scenarios.find(item => item.id === id);
  if (!scenario) return;
  input = structuredClone(scenario.input);
  $("scenario-note").textContent = scenario.note;
  renderInput();
  run();
}

for (const scenario of scenarios) $("scenario").add(new Option(scenario.title, scenario.id));
const custom = new Option("Custom memberships", "custom");
custom.disabled = true;
$("scenario").add(custom);
for (let count = 0; count <= 6; count++) $("job-count").add(new Option(count, count));
for (let count = 0; count <= 8; count++) $("category-count").add(new Option(count, count));
$("scenario").addEventListener("change", event => loadScenario(event.target.value));
$("job-count").addEventListener("change", event => {
  input.jobs = Array.from({ length: Number(event.target.value) }, (_, index) => input.jobs[index] || []);
  markCustom();
  renderInput();
});
$("category-count").addEventListener("change", event => {
  input.categories = Number(event.target.value);
  input.jobs = input.jobs.map(job => job.filter(category => category < input.categories));
  markCustom();
  renderInput();
});
$("run").addEventListener("click", run);

function invalidateValidation() {
  validationWorker?.();
  validationWorker = undefined;
  $("check-input").disabled = false;
  status("validation-status", "Input changed. Check it to see the program’s response.");
}
for (const scenario of invalidScenarios) {
  const button = element("button", scenario.title, "secondary");
  button.type = "button";
  button.addEventListener("click", () => {
    $("raw-input").value = JSON.stringify(scenario.input, null, 2);
    invalidateValidation();
  });
  $("invalid-presets").append(button);
}
$("raw-input").value = JSON.stringify(invalidScenarios[0].input, null, 2);
$("raw-input").addEventListener("input", invalidateValidation);
$("check-input").addEventListener("click", () => {
  invalidateValidation();
  let value;
  try { value = JSON.parse($("raw-input").value); }
  catch (error) { status("validation-status", `Invalid JSON: ${error.message}`, "error"); return; }
  $("check-input").disabled = true;
  status("validation-status", "Checking input in WASM.");
  validationWorker = execute(value, result => {
    validationWorker = undefined;
    $("check-input").disabled = false;
    if (!result.ok) status("validation-status", result.message, "error");
    else if (result.status === 1) status("validation-status", "WASM rejected the input: duplicate membership or invalid category ID (status 1).", "passed");
    else if (result.status === 2) status("validation-status", "WASM rejected the input: capacity exceeds 6 jobs or 8 categories (status 2).", "passed");
    else status("validation-status", `WASM accepted the input. Assignments: ${result.assignments.map(group => group === 0 ? "A" : "B").join(", ") || "none"}. All category differences are within ${result.bound}.`, "passed");
  });
});
loadScenario(scenarios[0].id);
