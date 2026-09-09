# GitHub Pages

The public project website is hosted at:

- [English](https://longweihan.github.io/ricci-curve-estimates/)
- [简体中文](https://longweihan.github.io/ricci-curve-estimates/zh/)

The repository uses **GitHub Actions** as its Pages publishing source. The workflow in [.github/workflows/pages.yml](../.github/workflows/pages.yml) runs on relevant changes to `main`, or manually from the repository's Actions tab.

It rebuilds the bilingual static site with `python3 scripts/build_site.py`, validates local links and anchors, and deploys `website/`. The build uses the bundled Lean declaration metadata, PDF, and KaTeX renderer. It needs Python and Node.js, with no npm installation or Lean compilation required for this publishing step.

## Update the website

Edit the canonical blueprint in `blueprint/blueprint.json`, its Chinese explanation in `website-template/zh-CN-blueprint.json`, or the templates in `website-template/`. Rebuild locally:

```sh
python3 scripts/build_site.py
```

Commit the source changes and generated `website/` files, then push to `main`. The Pages workflow validates and publishes the result. The language switch preserves the current page, source-line anchor, and search query where applicable.

If Lean statements change, first regenerate and verify the exported metadata using the documented Lean verification process. Publishing from an existing export does not perform a new proof check. The separate [Lean verification workflow](../.github/workflows/verify.yml) builds and audits the Lean project.

## Reuse in another repository

Enable **Settings → Pages → Source → GitHub Actions**, retain `main` as the publishing branch, and update the repository and website URLs in both READMEs and this guide. Site assets and navigation use relative links, so they work under a repository path such as `/ricci-curve-estimates/`.
