# hyper-watch

Hyper Watch: prices **every day** in a travel window on each run (all your home
airports to all the destination airports at once, any airline) and emails when a
day is exceptionally cheap.

- **Settings:** `hyperwatch.toml` (steal prices, dates, airports). Open it, click
  the pencil, change a number, then **Commit changes**.
- **Every day's current price:** the `latest.md` file on the `hyperwatch-data`
  branch. The watch keeps its memory on that branch too.
- **Schedule:** every 5 minutes (`.github/workflows/hyperwatch.yml`). GitHub skips most
  5-minute scheduled runs, so each run keeps checking every 5 minutes by itself for about
  an hour, then starts a fresh run (a new server, which also helps when Google turns one
  away). The 5-minute schedule only restarts the loop if it ever stops. This repo is
  public, so runs are free.
- **Email:** add the repo secrets `EMAIL_FROM`, `EMAIL_APP_PASSWORD` and `EMAIL_TO`
  (Settings, Secrets and variables, Actions). Without them, alerts arrive as GitHub
  issues on this repo instead.
- **To pause it:** Actions tab, click **Hyper Watch** on the left, click the
  **⋯** button, then **Disable workflow**. It also switches itself off once
  every travel day in the window has passed.

### Checking it offline

`python hyperwatch_selftest.py` walks the watch through made-up prices with no
internet and no email. Run it after changing `hyperwatch.py`.
