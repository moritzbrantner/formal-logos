import type { Locator } from "playwright";

// Counting a locator once, right after a navigation, reload, click or URL
// change, races client rendering: the page can still be hydrating, loading a
// graph bucket or committing the next React render (#1609). These helpers poll
// until the expected count appears (or the timeout expires) and otherwise
// fail with the last observed count. (No bun:test import: the typecheck
// includes this helper but not the test files.)

const TIMEOUT_MS = 15_000;
const INTERVAL_MS = 50;

/** Re-reads `read` until `accept` holds or the timeout expires; returns the last value. */
export async function eventually<T>(read: () => Promise<T>, accept: (value: T) => boolean, timeout = TIMEOUT_MS): Promise<T> {
  const deadline = Date.now() + timeout;
  let value = await read();
  while (!accept(value) && Date.now() < deadline) {
    await new Promise((resolve) => setTimeout(resolve, INTERVAL_MS));
    value = await read();
  }
  return value;
}

async function expectCountWhere(locator: Locator, accept: (count: number) => boolean, wanted: string): Promise<void> {
  const count = await eventually(() => locator.count(), accept);
  if (!accept(count)) {
    throw new Error(`Expected ${locator} to match ${wanted} elements within ${TIMEOUT_MS} ms; last count ${count}`);
  }
}

/** Asserts that the locator eventually matches exactly `expected` elements. */
export function expectCount(locator: Locator, expected: number): Promise<void> {
  return expectCountWhere(locator, (count) => count === expected, `exactly ${expected}`);
}

/** Asserts that the locator eventually matches more than `minimum` elements. */
export function expectCountAbove(locator: Locator, minimum: number): Promise<void> {
  return expectCountWhere(locator, (count) => count > minimum, `more than ${minimum}`);
}

/** Asserts that the locator eventually matches at least `minimum` elements. */
export function expectCountAtLeast(locator: Locator, minimum: number): Promise<void> {
  return expectCountWhere(locator, (count) => count >= minimum, `at least ${minimum}`);
}
