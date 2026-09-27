export const scenarios = [
  {
    id: "overlap", title: "Six overlapping jobs",
    note: "Each job belongs to two categories. Each category contains four jobs, exceeding the difference bound of three.",
    input: { categories: 3, jobs: [[0, 1], [0, 1], [0, 2], [0, 2], [1, 2], [1, 2]] },
  },
  {
    id: "odd", title: "An odd category count",
    note: "Five jobs share one category. A difference of one is unavoidable, and the bound is one.",
    input: { categories: 1, jobs: [[0], [0], [0], [0], [0]] },
  },
  {
    id: "repeated", title: "Two categories with the same jobs",
    note: "Categories A and B contain the same five jobs. The last job belongs only to C. Repeated category sets are valid.",
    input: { categories: 3, jobs: [[0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [2]] },
  },
  {
    id: "cycle", title: "A cycle that fits in one group",
    note: "Every pair of jobs shares a category. Each category has two jobs, within the bound of three. This algorithm puts all three jobs in Group B.",
    input: { categories: 3, jobs: [[0, 1], [1, 2], [0, 2]] },
  },
  {
    id: "unassigned", title: "Jobs with no categories",
    note: "These six jobs have no memberships. Maximum overlap and category differences are zero. All jobs enter Group B.",
    input: { categories: 3, jobs: [[], [], [], [], [], []] },
  },
  {
    id: "empty", title: "An empty job list",
    note: "With no jobs, both groups are empty. The three declared categories each have zero jobs.",
    input: { categories: 3, jobs: [] },
  },
];

export const invalidScenarios = [
  { title: "Duplicate membership", input: { categories: 2, jobs: [[0, 0]] }, status: 1 },
  { title: "Category outside the range", input: { categories: 2, jobs: [[2]] }, status: 1 },
  { title: "Seven jobs", input: { categories: 1, jobs: [[0], [0], [0], [0], [0], [0], [0]] }, status: 2 },
];

export function encode(input) {
  if (!input || typeof input !== "object" || Array.isArray(input) ||
      Object.keys(input).some(key => !["jobs", "categories"].includes(key)) ||
      !Number.isSafeInteger(input.categories) || input.categories < 0 || !Array.isArray(input.jobs)) {
    throw new Error("Use a category count and an array of job memberships.");
  }
  if (input.jobs.length > 32) throw new Error("The demo accepts at most 32 input rows for validation tests.");
  const words = [input.jobs.length, input.categories];
  for (const job of input.jobs) {
    if (!Array.isArray(job) || job.some(id => !Number.isSafeInteger(id) || id < 0)) {
      throw new Error("Category IDs must be nonnegative integers.");
    }
    if (words.length + job.length + 1 > 256) throw new Error("The demo accepts at most 256 input words.");
    words.push(job.length, ...job);
  }
  return words;
}

export function check(input, result) {
  if (!Array.isArray(result) || result.length === 0 || result.some(word => !Number.isSafeInteger(word) || word < 0)) {
    throw new Error("WASM returned an invalid word array.");
  }
  const status = result[0];
  if (status !== 0) {
    if (result.length !== 1 || ![1, 2, 3].includes(status)) throw new Error("WASM returned an unknown status.");
    if (status === 3) throw new Error("WASM reported an internal failure.");
    return { status, result };
  }
  if (input.jobs.length > 6 || input.categories > 8 || result.length !== input.jobs.length + 2) {
    throw new Error("WASM returned a result outside the supported bounds.");
  }
  const assignments = result.slice(2);
  if (assignments.some(group => group !== 0 && group !== 1)) throw new Error("WASM returned an invalid group.");
  const overlap = Math.max(0, ...input.jobs.map(job => job.length));
  if (result[1] !== overlap) throw new Error("The returned overlap disagrees with the memberships.");
  const bound = overlap === 0 ? 0 : 2 * overlap - 1;
  const counts = Array.from({ length: input.categories }, (_, category) => ({ category, groups: [0, 0], total: 0 }));
  input.jobs.forEach((job, index) => {
    if (new Set(job).size !== job.length) throw new Error("WASM accepted a duplicate membership.");
    for (const category of job) {
      if (category >= input.categories) throw new Error("WASM accepted an invalid category.");
      counts[category].groups[assignments[index]]++;
      counts[category].total++;
    }
  });
  for (const row of counts) {
    row.difference = Math.abs(row.groups[0] - row.groups[1]);
    if (row.difference > bound) throw new Error(`Category ${row.category} exceeds the difference bound.`);
  }
  return { status, result, assignments, overlap, bound, counts };
}
