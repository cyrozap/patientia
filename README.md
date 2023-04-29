# patientia

_patientia_ is a Rust library for parsing PDF files.

**WARNING**: This library is not ready for production use! If you just want a
general-purpose PDF-parsing library, please look elsewhere. This library is
incomplete, and it is not yet able to parse most PDF files. And until version
1.0, each version change will include breaking API changes, so if you do choose
to use this as a dependency in your own project, please pin the version exactly.


## Introduction

The name "patientia" comes from the Latin word for "patience", a personal
quality needed when dealing with frustrating nightmares like the PDF
specification and real-world PDF files.

Version 0.1.0 of this library was written when the author had very little
experience with Rust, so the API is kind of a pain to use. Thanks to the lessons
learned from writing this initial version, future versions will have a much more
ergonomic API.


## License

_patientia_ is published under the terms of the [GNU General Public License,
version 3 or later](COPYING.txt).
