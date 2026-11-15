import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

import { uid } from "./corpus-records";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const caseRoot = uid("statement", "STMT-CATHOLICISM-TRUE");

beforeAll(async () => {
  server = Bun.serve({
    port: 0,
    async fetch(request) {
      const requested = decodeURIComponent(new URL(request.url).pathname);
      if (basePath && !requested.startsWith(`${basePath}/`)) return new Response("Not found", { status: 404 });
      const pathname = basePath ? requested.slice(basePath.length) : requested;
      const relative = pathname.endsWith("/") ? `${pathname}index.html` : pathname;
      const file = path.resolve(root, `.${relative}`);
      if (!file.startsWith(`${root}${path.sep}`)) return new Response("Not found", { status: 404 });
      const artifact = Bun.file(file);
      return await artifact.exists() ? new Response(artifact) : new Response("Not found", { status: 404 });
    },
  });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

test("the case-root tree re-roots by click, marks truncation and lists definitions", async () => {
  const page = await browser.newPage({ viewport: { width: 1400, height: 1000 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(new URL(`${basePath}/tree/`, server.url).toString());
  await page.locator(`#tree-root[data-root-id="${caseRoot}"]`).waitFor();
  expect(await page.locator('[data-testid="tree-truncation"]').count()).toBeGreaterThan(0);
  await page.locator('[data-testid="tree-truncation"]').first().scrollIntoViewIfNeeded();
  expect(await page.locator('[data-testid="tree-truncation"]').first().isVisible()).toBe(true);
  const definitions = page.locator('[data-testid="tree-definitions"] li');
  expect(await definitions.count()).toBeGreaterThan(0);
  await definitions.first().locator(`a[href^="${basePath}/definitions/"]`).waitFor();
  expect(await page.locator('[data-testid="tree-formal-status"]').first().textContent()).toMatch(/Lean definition|primitive|no Lean|not yet computed/);

  const next = page.locator('[data-testid="tree-statement"][data-prebuilt="true"]:not([data-role="root"])').first();
  const nextId = await next.getAttribute("data-statement-id");
  expect(nextId).toBeTruthy();
  await next.scrollIntoViewIfNeeded();
  await next.click();
  await page.locator(`#tree-root[data-root-id="${nextId}"]`).waitFor();
  const url = new URL(page.url());
  expect(url.pathname).toBe(`${basePath}/tree/`);
  expect(url.searchParams.get("id")).toBe(nextId);
  expect(await page.locator(`[data-testid="tree-statement"][data-role="root"][data-statement-id="${nextId}"]`).count()).toBe(1);
  // The former root, when the budget leaves room for it, is now a dependent of the new root.
  const former = page.locator(`[data-testid="tree-statement"][data-statement-id="${caseRoot}"]`);
  if (await former.count()) expect(await former.getAttribute("data-role")).toBe("dependent");
  await page.goBack();
  await page.locator(`#tree-root[data-root-id="${caseRoot}"]`).waitFor();
  expect(errors).toEqual([]);
  await page.close();
}, 60000);

test("a statement without a prebuilt tree gives the local command, and statement pages link the tree", async () => {
  const page = await browser.newPage();
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const id = "00000000-0000-4000-8000-000000000000";
  await page.goto(new URL(`${basePath}/tree/?id=${id}`, server.url).toString());
  await page.getByRole("heading", { name: "This tree is generated locally" }).waitFor();
  expect(await page.getByText(`target/release/truth tree ${id}`).count()).toBe(1);
  await page.goto(new URL(`${basePath}/statements/${caseRoot}/`, server.url).toString());
  await page.getByRole("link", { name: "Argument tree with this proposition as root →" }).click();
  await page.locator(`#tree-root[data-root-id="${caseRoot}"]`).waitFor();
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
