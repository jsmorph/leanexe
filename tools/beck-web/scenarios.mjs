export const scenarios = [
  {
    id: "overlap", title: "32 jobs with overlapping categories",
    note: "Each job belongs to three of 16 categories. Several category counts exceed the discrepancy bound of five.",
    input: {"categories":16,"jobs":[[0,1,2],[2,4,11],[0,1,15],[8,10,11],[2,6,15],[5,8,11],[3,5,14],[4,13,14],[5,10,13],[5,7,12],[4,7,13],[5,8,10],[1,12,15],[1,4,5],[3,4,12],[4,5,9],[4,8,15],[1,4,7],[6,7,12],[2,7,8],[3,8,10],[1,13,14],[1,7,14],[2,11,12],[6,7,15],[0,4,14],[0,2,6],[10,12,15],[0,6,14],[7,9,10],[6,10,14],[3,7,12]]},
  },
  {
    id: "odd", title: "65 jobs in one category",
    note: "An odd category size forces a difference of at least one. With overlap one, the bound is exactly one.",
    input: { categories: 1, jobs: Array.from({ length: 65 }, () => [0]) },
  },
  {
    id: "repeated", title: "Repeated categories and an isolated job",
    note: "Categories A and B contain the same 31 jobs. One isolated job belongs to C. Dependent category constraints must still yield a direction.",
    input: { categories: 3, jobs: [...Array.from({ length: 31 }, () => [0, 1]), [2]] },
  },
  {
    id: "cycle", title: "An odd cycle",
    note: "Each job belongs to its two neighboring categories. Each category contains two jobs, within the bound of three. Equal total group sizes are optional.",
    input: { categories: 17, jobs: Array.from({ length: 17 }, (_, i) => [i, (i + 1) % 17]) },
  },
  {
    id: "unassigned", title: "64 jobs with no memberships",
    note: "Maximum overlap and all category differences are zero. Every job still receives an assignment.",
    input: { categories: 8, jobs: Array.from({ length: 64 }, () => []) },
  },
  {
    id: "empty", title: "An empty job list",
    note: "Both groups are empty. All declared categories have zero jobs.",
    input: { categories: 16, jobs: [] },
  },
];

export const invalidScenarios = [
  { title: "Duplicate membership", input: { categories: 2, jobs: [[0, 0]] }, status: 1 },
  { title: "Category outside the range", input: { categories: 2, jobs: [[2]] }, status: 1 },
  { title: "Incidence array exceeds memory", input: { categories: 536870912, jobs: [[]] }, status: 2 },
];

export function encode(input) {
  if (!input || typeof input !== "object" || Array.isArray(input) ||
      Object.keys(input).some(key => !["jobs", "categories"].includes(key)) ||
      !Number.isSafeInteger(input.categories) || input.categories < 0 || !Array.isArray(input.jobs)) {
    throw new Error("Use a category count and an array of job memberships.");
  }
  if (input.jobs.length > 128) throw new Error("The demo accepts at most 128 input rows.");
  const words = [input.jobs.length, input.categories];
  for (const job of input.jobs) {
    if (!Array.isArray(job) || job.some(id => !Number.isSafeInteger(id) || id < 0)) {
      throw new Error("Category IDs must be nonnegative integers.");
    }
    if (words.length + job.length + 1 > 8192) throw new Error("The demo accepts at most 8192 input words.");
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
  if (result.length !== input.jobs.length + 2) {
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
