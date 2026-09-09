---
name: relay
description: タスクを context 上限に阻まれず完遂まで無人で自走する。1 セッション（leg）が重くなる前に handoff → 新セッション起動 → carryon で引き継ぎ、を完遂まで自動で連鎖する。ユーザーが「完遂まで自走して」「最後まで自走して完遂して」「無人で最後までやって」「セッションをまたいで完遂して」「リレーして」「/relay」と言ったときに起動する。鍵語は「完遂まで/最後まで/無人で/セッションをまたいで」。単なる「自走して」では起動しない（carryon の通常自走と区別）。
---

# relay — run a task to completion across sessions, unattended

A long task dies at the context ceiling, not at the work. This skill removes that ceiling
by chaining sessions: each **leg** works until its judgement starts to degrade, then writes
a handoff, starts a fresh session, and hands it the baton — repeating until the goal is
met. The user states the goal once and walks away.

**This is a self-replicating loop**, so the guardrails are the load-bearing part, not the
chaining. A leg that cannot honour the leg cap, the no-progress check, and the
one-commit-per-leg floor must terminate rather than spawn.

## Trigger

What separates relay from `carryon`'s ordinary self-driving is the phrase
**「完遂まで / 最後まで / 無人で / セッションをまたいで」**. A bare 「自走して」 is not enough —
that is what `carryon` already does.

- 「<タスク> を完遂まで自走して」「最後まで自走して完遂して」
- 「無人で最後までやって」「放っておいても完遂して」
- 「セッションをまたいで完遂して」「リレーして」「何セッションかけても完遂して」
- `/relay <タスク> [cap=N]` — cap defaults to 8

## Which leg is this

The handoff file is the only state that survives a leg. Resolve its path first — it lives
outside the repository, keyed by the working directory, and `carryon` and `handoff` derive
the same path the same way:

```bash
printf '%s/.claude/handoffs/%s.md\n' "$HOME" "$(printf '%s' "$PWD" | tr -c 'a-zA-Z0-9' '-')"
```

- **A later leg** — that file has a `## Relay control` section with `Mode: ON`. A
  predecessor started you. Run the lifecycle from step 1.
- **The first leg** — no live Relay control. The user just invoked you. Draft the Relay
  control block (`Leg: 1 / cap K`, `Predecessor: none`, `Goal: <task>`, empty ledger) and
  enter the lifecycle at step 3. Do not run `carryon`: the goal is in front of you.

## The lifecycle of one leg

1. **Restore (later legs only).** Run `Skill(carryon)`. It reads the handoff, restores the
   task list, checks whether the repo moved, announces the next move and starts working.
   **Restoration lives in `carryon`; relay does not reimplement it.**
2. **Retire the predecessor (later legs only).** Once `carryon` is genuinely working —
   files opened, first edit made, not merely started — close the pane named by
   `Predecessor`:
   ```bash
   herdr pane close <predecessor-pane-id>
   ```
   Skip this when `Predecessor: none`. The successor closes the predecessor, rather than
   the predecessor closing itself, because a parent that dies during a failed spawn ends
   the chain with nobody left to notice.
3. **Work.** Everything `carryon` would do, under this repository's rules in `CLAUDE.md`:
   push straight to main, commit autonomously, no branches, no PRs.
4. **Decide: terminate or hand over.** Follow the reading below.

## Reading carryon's stop conditions

A relay leg inherits `carryon`'s self-driving whole, and changes exactly one of its three
stop conditions.

- **The work is done** → terminate. Set `Mode: DONE` with a one-or-two-line summary,
  notify, stop.
- **A decision is the user's to make** → terminate. Set `Mode: PAUSED`, write down exactly
  what you need decided, notify, stop. **Do not start another leg** — a fresh session
  stalls at the same fork, having lost the context that would let it argue the case.
  Do not block on `AskUserQuestion` either: nobody is watching.
- **Context is running short** → **do not terminate.** This is the one condition relay
  overrides. Instead of asking the user for a fresh session, start one yourself — see
  *Handover* below. This override is the whole of what relay adds.

One relay-specific signal joins them: **a second malformed tool call in a leg** is reliable
evidence of a degraded context. Treat it as the third condition and hand over.

## Handover

When the context is running short, in this order:

1. **Get to a state the next leg can trust.** This repository pushes straight to main, so
   a leg that pushes red leaves main red with no reviewer in the way. Run every gate
   before pushing — the list is in `CLAUDE.md` and matches `.github/workflows/ci.yml`:
   ```sh
   pnpm lean:build && pnpm lean:emit && pnpm typecheck && pnpm test && pnpm lint \
     && pnpm package:check && pnpm template:check \
     && git diff --exit-code -- packages/verified-example
   ```
   All green → commit and push. Any red → fix it, or revert to the last green commit and
   record in the ledger what you backed out and why. **Never hand a dirty or red tree to
   the next leg**: `carryon` trusts the repo over the handoff, so a broken tree becomes the
   successor's starting assumption.
2. **Append to the ledger.** `r<N>: <what landed> (<commit hash>)`.
3. **Check for no progress.** If the last two legs, yours included, produced no commit, no
   completed task and no new measurement, set `Mode: ABORTED`, notify, and stop. Do not
   hand over. Two empty legs mean the chain is not converging, and a third will not either.
4. **Check the leg cap.** If `N + 1 > cap`, set `Mode: PAUSED` ("leg cap reached, continue?"),
   notify, and stop.
5. **Write the handoff.** Overwrite the file at the path above, in the shape the `handoff`
   skill defines, plus the Relay control block. Write it yourself rather than calling
   `Skill(handoff)` — inside Herdr that skill hands its own baton with `/carryon` and
   retires this pane, which is not the succession relay needs.
6. **Start the next leg.** Name it `<goal>-r<N+1>` — a short hyphenated name matching
   `[a-z][a-z0-9_-]{0,31}`, unique among `herdr agent list`.
   ```bash
   herdr pane split --current --direction right --cwd "$PWD" --no-focus   # → .result.pane.pane_id
   herdr pane run <pane-id> 'safe-claude --name <goal>-r<N+1>'
   herdr agent list          # re-run until the pane appears; the detector takes a few seconds
   herdr agent rename <pane-id> <goal>-r<N+1>
   herdr agent prompt <goal>-r<N+1> "/relay"
   herdr agent wait <goal>-r<N+1> --until working --timeout 15000
   ```
   `--cwd "$PWD"` is not optional: the handoff path is keyed by the working directory, and a
   successor started elsewhere derives a different path and finds nothing. The prompt is
   `/relay`, not `/carryon` — `/carryon` alone would restore the work and then stop at the
   next context ceiling, ending the chain.
7. **Confirm it took the baton.** `agent prompt` returns before the successor paints
   anything, so read it: `herdr agent read <goal>-r<N+1> --source recent-unwrapped --lines 40`.
   If it will not start after a couple of attempts, stop and notify. A handoff file nobody
   reads beats a chain nobody notices has died.
8. **Go idle.** Make no further tool calls — a second session touching the same worktree
   races on `.git/index.lock`. The successor closes your pane at its step 2.

## Guardrails

Unattended means these are not negotiable:

- **Leg cap** — 8 by default, `cap=N` at invocation. Exceeded → `PAUSED`.
- **No progress** — two consecutive legs with nothing measurable → `ABORTED`.
- **One commit per leg** — if a leg cannot land anything, it must say why in the ledger.
  That entry is what the no-progress check reads.
- **Never push red.** The gate list above, in full. A partial run is not a result.
- **Every termination notifies.** `DONE`, `PAUSED` and `ABORTED` alike, via
  `PushNotification` — nobody is at the keyboard.
- When in doubt, terminate and notify. Handing the work back to a human is always cheaper
  than another leg spent going the wrong way.

## The Relay control block

Appended to the handoff file for as long as a chain is live:

```
## Relay control
- Mode: ON | DONE | PAUSED | ABORTED
- Goal: <what counts as finished>
- Leg: N / cap K
- Predecessor: <pane id, or none>
- Stop-on: completion | user-decision | no-progress×2 | leg-cap
- Progress ledger:
  - r1: <what landed / commit hash>
  - r2: <what landed / commit hash>
```

`Mode: ON` doubles as the reminder of the override. Every leg re-reads it on startup, so
"context pressure means hand over, not stop" is re-injected from the file rather than
relied on to survive in a context that is by then degraded.

## Principles

- **Guardrails first.** The chain runs itself; the caps are what keep it from running away.
- **One live leg at a time.** Start the successor and go idle. Two sessions in one worktree
  corrupt each other's git state.
- **Do not reimplement `carryon`.** Relay adds the override of stop condition #3 and the
  handover. Everything else is `carryon`'s.
- **Green before handover.** The next leg inherits the tree, and it will believe it.
