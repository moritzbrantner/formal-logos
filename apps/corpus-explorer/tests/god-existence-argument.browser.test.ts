import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";
import { expectCount } from "./browser-waits";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const argumentId = "8df25074-38c2-4672-a9e7-3f4cc2a97367";
const closedCollectionsId = "20babef7-6ae7-4b48-b72a-f417e8e63136";
const resultId = "dbcd7ada-0d54-4346-8fe8-838b8cca8b33";

beforeAll(async () => {
  server = Bun.serve({ port: 0, async fetch(request) {
    let pathname = decodeURIComponent(new URL(request.url).pathname);
    if (basePath && pathname.startsWith(basePath + "/")) {
      pathname = pathname.slice(basePath.length);
    }
    const file = path.resolve(root, "." + (pathname.endsWith("/") ? pathname + "index.html" : pathname));
    if (!file.startsWith(root + path.sep) || !(await Bun.file(file).exists())) {
      return new Response("Not found", { status: 404 });
    }
    return new Response(Bun.file(file));
  } });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

test("the closed-collection GOD_4 argument exposes all its inputs and supports shareable withholding", async () => {
  const page = await browser.newPage({ viewport: { width: 390, height: 844 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(new URL(basePath + "/case/god-exists/", server.url).toString());
  await page.locator(`#argument-${argumentId}`).getByRole("link", { name: "Inspect argument and compare premises" }).click();
  await page.getByRole("heading", { name: /common uncaused.*source/ }).waitFor();

  const inputSelect = page.getByLabel("Withhold one input");
  const outcome = page.getByRole("status");
  const available = "A registered argument reaches the conclusion from the retained inputs.";
  const unavailable = "No registered argument reaches the conclusion from the retained inputs.";
  await expectCount(inputSelect.getByRole("option"), 17);
  await page.getByText(available, { exact: true }).waitFor();
  expect(await outcome.textContent()).toBe(available);
  expect(await page.getByRole("link", { name: /godExistsFromClosedCollections/ }).getAttribute("href"))
    .toContain(`/results/${resultId}/#lean-evidence`);
  expect(await page.getByRole("link", { name: "Challenge source" }).getAttribute("href"))
    .toMatch(/ClosedEsseSourceGod\/Challenge\.lean#L\d+$/);
  expect(await page.getByRole("link", { name: "Solution source" }).getAttribute("href"))
    .toContain("ClosedEsseSourceGod/Solution.lean");
  expect(await page.getByRole("link", { name: /no nonempty collection of actual esse bearers/ }).getAttribute("href"))
    .toContain(`/case/god-exists/premises/${closedCollectionsId}/`);

  await inputSelect.selectOption(closedCollectionsId);
  await page.waitForURL((url) => url.searchParams.get("without") === closedCollectionsId);
  await page.getByText(unavailable, { exact: true }).waitFor();
  await page.getByText("Required inputs still unavailable").waitFor();
  await page.reload();
  await page.getByText(unavailable, { exact: true }).waitFor();
  expect(await inputSelect.inputValue()).toBe(closedCollectionsId);

  await inputSelect.selectOption("");
  await page.getByText(available, { exact: true }).waitFor();
  expect(new URL(page.url()).searchParams.has("without")).toBe(false);
  await page.goBack();
  await page.getByText(unavailable, { exact: true }).waitFor();
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  expect(errors).toEqual([]);
  await page.close();
}, 90000);

test("a withheld input can be unnecessary for another route or recovered for the selected route", async () => {
  const page = await browser.newPage();
  const fullDescriptionId = "fd1f7e75-2269-5206-9f36-8f4f3c667566";
  const alternateRouteId = "0e8e37dc-4037-450f-8172-a26eff2d7113";
  const recoveredInputId = "ca075552-10fc-5d18-afb8-f0344bdcf77c";
  const url = new URL(`${basePath}/case/god-exists/arguments/${fullDescriptionId}/`, server.url);
  url.searchParams.set("without", "101bdd62-7cd0-5923-8f03-d9d443f4ba51");
  await page.goto(url.toString());
  await page.getByText("The selected argument is missing one or more required inputs.").waitFor();
  expect(await page.getByRole("status").textContent()).toBe("A registered argument reaches the conclusion from the retained inputs.");
  const alternate = page.getByRole("link", { name: /universal esse cause with restricted perfection transfer/ });
  expect(await alternate.getAttribute("href")).toContain(`/case/god-exists/arguments/${alternateRouteId}/`);

  await page.getByLabel("Withhold one input").selectOption(recoveredInputId);
  await page.getByText("The selected argument can be applied.").waitFor();
  await page.getByText("Withheld inputs derived from the retained inputs").waitFor();
  await page.getByText("One derivation in dependency order", { exact: true }).click();
  const steps = page.getByRole("list", { name: "Derivation steps" });
  await expectCount(steps.getByRole("listitem"), 2);
  expect(await steps.getByRole("link").last().textContent()).toContain("via full description");
  await page.close();
}, 90000);
