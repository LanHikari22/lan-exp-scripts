<div align="center">
  lan-exp-scripts
  <p>A repository for experimental scripts</p>
</div>

<p align="center">
  <a href="https://opensource.org/licenses/MIT">
    <img src="https://img.shields.io/badge/License-MIT-brightgreen.svg"
      alt="License: MIT" />
  </a>
  <a href="https://buymeacoffee.com/lan22h">
    <img src="https://img.shields.io/static/v1?label=Buy me a coffee&message=%E2%9D%A4&logo=BuyMeACoffee&link=&color=greygreen"
      alt="Buy me a Coffee" />
  </a>
</p>

<div align="center">
  <sub>Built with ❤︎ by Mohammed Alzakariya
</div>
<br>

- [What is this?](#what-is-this)
- [Folder Structure](#folder-structure)
  - [Scripts](#scripts)
  - [Files](#files)
  - [Templates](#templates)
  - [Examples](#examples)
- [Contributing](#contributing)
- [License](#license)


# What is this?

I store experimental/temporary scripts I write in this repository. It provides versioning and a public reference for them.

# Folder Structure

## Scripts

Scripts are meant to be functional code that performs some purpose I need. Whether for tooling or experimentation or otherwise.

`scripts/{YYYY}/persistent` contains scripts written in YYYY (like 2025) that are expected to be referenced. For example common utilities can be put here.

`scripts/{YYYY}/weekly/` contains scripts that are indexed by the week number according to the [ISO standard](https://www.epochconverter.com/weeks/2025). 

The syntax for this notation is `Wk-{Week}-NNN-Description` where NNN is 0-padded index value. persistent scripts use the same indexing scheme but without the `Wk-{Week}-`. 

Other folders also often follow the same scheme here.

## Files

In the `scripts/` folder, the expectation is some source code that performs some function.

In `files`, this restriction is relaxed. This could host supplementary or explorative code for puzzles and the like.

## Templates

In `templates/` we have files that are meant to be used for some common tasks for example creating a python app with argparse.

In addition to the scheme in `scripts/`, this also adds `templates/YYYY/topics/{topic}/{persistent/weekly}/` to group the templates by a broader topic. 

For example, `templates/2025/topics/py3/persistent/000-argparse/`.

Sometimes it may be necessary to add entries at different tree depths of the topic tree. For example:

```
  py3
    {py3 entries ...}
    unittest
      {unittest entries ...}
```

In this case we use a special topic called `topic` to refer to the parent as the topic:

`templates/2025/topics/py3/topic/persistent/000-argparse/`
`templates/2025/topics/py3/unittest/persistent/000-argparse-unittest/`


## Examples

In `examples/` we reproduce code. This is often external tutorial and example code to perform various functions, or errors of some kind. This is somewhat similar to [rs_repro](https://github.com/LanHikari22/rs_repro) except it's more general and not focused on rust.

## Other

Others are like `examples/`, and include `tutorials/`


# Contributing

All contributions are welcome! 

If there is anything here you would like to be developed further into its own project, or if you have any requests, recommendations, or comments, please let me know by [opening an issue](https://github.com/LanHikari22/rs_repro/issues/new).

Please feel free to contact me by opening an issue ticket or emailing lanhikarixx@gmail.com if you want to chat.

# License

This work is licensed under the [MIT license](https://opensource.org/licenses/mit-license.php) © 2025 Mohammed Alzakariya.

