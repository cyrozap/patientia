// SPDX-License-Identifier: GPL-3.0-or-later

/*
 *  src/lib.rs - PDF parsing functionality.
 *  Copyright (C) 2018-2021, 2023  Forest Crossman <cyrozap@gmail.com>
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

use std::collections::HashMap;
use std::convert::TryFrom;

extern crate nom;
use nom::*;

#[derive(Debug, PartialEq, Eq)]
pub enum PdfVersion {
    V1P0,
    V1P1,
    V1P2,
    V1P3,
    V1P4,
    V1P5,
    V1P6,
    V1P7,
    UNKNOWN,
}

#[derive(Debug, PartialEq)]
pub struct PdfComment {
    comment: Vec<u8>,
}

#[derive(Debug, PartialEq)]
pub struct PdfWhitespace {
    whitespace: Vec<u8>,
}

#[derive(Debug, PartialEq)]
pub enum PdfNumber {
    PdfInteger(i32),
    PdfReal(f32),
}

pub type PdfName = Vec<u8>;

pub type PdfArray = Vec<PdfObject>;

pub type PdfDictionary = HashMap<PdfName, PdfObject>;

#[derive(Debug, PartialEq)]
pub struct PdfStream {
    pub dictionary: PdfDictionary,
    pub data: Vec<u8>,
}

#[derive(Debug, PartialEq)]
pub enum PdfDirectObject {
    PdfBool(bool),
    PdfString(Vec<u8>),
    PdfNumber(PdfNumber),
    PdfName(PdfName),
    PdfArray(PdfArray),
    PdfDictionary(PdfDictionary),
    PdfStream(PdfStream),
    PdfNull(),
}

#[derive(Debug, PartialEq)]
pub struct PdfIndirectObject {
    pub obj_num: u64,
    pub gen_num: u16,
    pub object: PdfDirectObject,
}

#[derive(Debug, PartialEq)]
pub struct PdfIndirectObjectReference {
    pub obj_num: u64,
    pub gen_num: u16,
}

#[derive(Debug, PartialEq)]
pub enum PdfObject {
    PdfDirectObject(PdfDirectObject),
    PdfIndirectObject(PdfIndirectObject),
    PdfIndirectObjectReference(PdfIndirectObjectReference),
}

#[derive(Debug, PartialEq)]
pub enum PdfElement {
    PdfComment(PdfComment),
    PdfWhitespace(PdfWhitespace),
    PdfIndirectObject(PdfIndirectObject),
}

#[derive(Debug, PartialEq)]
pub struct PdfHeader {
    version: PdfVersion,
}

#[derive(Debug, PartialEq)]
pub struct PdfBody {
    pub objects: Vec<PdfIndirectObject>,
}

#[derive(Debug, PartialEq)]
pub struct PdfXrtInUseObject {
    offset: u64,
    gen: u16,
}

#[derive(Debug, PartialEq)]
pub struct PdfXrtFreeObject {
    obj_num: u64,
    gen: u16,
}

#[derive(Debug, PartialEq)]
pub enum PdfXrtSubsectionEntry {
    InUseObject(PdfXrtInUseObject),
    FreeObject(PdfXrtFreeObject),
}

#[derive(Debug, PartialEq)]
pub struct PdfXrtSubsection {
    first_obj_num: u64,
    num_entries: u64,
    entries: Vec<PdfXrtSubsectionEntry>,
}

#[derive(Debug, PartialEq)]
pub struct PdfXrtSection {
    subsections: Vec<PdfXrtSubsection>,
}

#[derive(Debug, PartialEq)]
pub struct PdfXrt {
    sections: Vec<PdfXrtSection>,
}

#[derive(Debug, PartialEq)]
pub struct PdfTrailer {
    pub dictionary: PdfDictionary,
    startxref: u64,
}

#[derive(Debug, PartialEq)]
pub struct PdfFile {
    pub header: PdfHeader,
    pub body: PdfBody,
    pub xrt: PdfXrt,
    pub trailer: PdfTrailer,
}

// PDF 32000-1:2008 standard: 7.2.2 Character Set, newline characters
named!(
    pdf_eol,
    alt!(complete!(tag!("\r\n")) | tag!("\n") | tag!("\r"))
);

// PDF 32000-1:2008 standard: 7.2.2 Character Set, white-space characters
fn is_whitespace(c: u8) -> bool {
    match c {
        b'\x00' => true,
        b'\x09' => true,
        b'\x0A' => true,
        b'\x0C' => true,
        b'\x0D' => true,
        b' ' => true,
        _ => false,
    }
}

// PDF 32000-1:2008 standard: 7.2.2 Character Set, white-space characters
named!(pdf_whitespace<&[u8], PdfWhitespace>,
    do_parse!(
        whitespace: take_while!(is_whitespace) >>
        (PdfWhitespace{whitespace: whitespace.to_vec()})
    )
);

// PDF 32000-1:2008 standard: 7.2.3 Character Set, comments
named!(pdf_comment<&[u8], PdfComment>,
    do_parse!(
        comment: preceded!(
            tag!("%"),
            alt_complete!(
                take_until!("\r") |
                take_until!("\n")
            )
        ) >>
        (PdfComment{comment: comment.to_vec()})
    )
);

named!(
    pdf_separator,
    recognize!(many1!(alt!(
        pdf_comment    => { |_| () } |
        pdf_whitespace => { |_| () }
    )))
);

// PDF 32000-1:2008 standard: 7.3.2 Boolean Objects
named!(pdf_bool<&[u8], bool>,
    alt!(
        tag!("true")  => { |_| true  } |
        tag!("false") => { |_| false }
    )
);

// PDF 32000-1:2008 standard: 7.3.3 Numeric Objects, integers
named!(pdf_integer<&[u8], i32>,
    flat_map!(
        recognize!(
            tuple!(
                opt!( alt!( char!('+') | char!('-') ) ),
                digit
            )
        ),
        parse_to!(i32)
    )
);

// PDF 32000-1:2008 standard: 7.3.3 Numeric Objects, real values
named!(pdf_real<&[u8], f32>,
    flat_map!(
        recognize!(
            tuple!(
                opt!( alt!( char!('+') | char!('-') ) ),
                alt!(
                    value!((), tuple!( digit, char!('.'), digit )) |
                    value!((), tuple!( char!('.'), digit )) |
                    value!((), tuple!( digit, char!('.') ))
                )
            )
        ),
        parse_to!(f32)
    )
);

named!(pdf_number<&[u8], PdfNumber>,
    do_parse!(
        number: alt_complete!(
            pdf_real     => { |r: f32| PdfNumber::PdfReal(r)    } |
            pdf_integer  => { |r: i32| PdfNumber::PdfInteger(r) }
        ) >>
        (number)
    )
);

// PDF 32000-1:2008 standard: 7.3.4 String Objects

// PDF 32000-1:2008 standard: 7.3.4.2 Literal Strings, escape sequences
fn parse_literal_string(v: &[u8]) -> IResult<&[u8], Vec<u8>> {
    // TODO: Needs improvement++.
    let mut ret = Vec::new();
    let mut open_par = 0;
    let mut escaped = false;
    let mut octal_value = 0;
    let mut octal_digit_idx = 0;

    let mut idx = 0;
    for (i, c) in v.iter().enumerate() {
        //println!("{}, {}, {}, {}, {:?}", len, idx, open_par, escaped, ret);
        idx = i;
        if escaped {
            let val = match c {
                b'n' => Some(b'\n'),
                b'r' => Some(b'\r'),
                b't' => Some(b'\t'),
                b'b' => Some(b'\x08'),
                b'f' => Some(b'\x0C'),
                b'(' => Some(*c),
                b')' => Some(*c),
                b'\\' => Some(*c),
                _ => None,
            };
            if val.is_some() {
                ret.push(val.unwrap());
                escaped = false;
                continue;
            }

            if c == &b'\n' || c == &b'\r' {
                if v[i..i + 2] != b"\r\n"[..] {
                    escaped = false;
                }
                continue;
            }

            if is_oct_digit(*c) {
                octal_digit_idx += 1;
                octal_value = (octal_value << 3) | (c - b'0');
                if octal_digit_idx == 3 || !is_oct_digit(v[i + 1]) {
                    ret.push(octal_value);
                    octal_value = 0;
                    octal_digit_idx = 0;
                    escaped = false;
                }
            }
            continue;
        }

        match c {
            b'(' => {
                open_par += 1;
            }
            b')' => {
                if open_par <= 0 {
                    break;
                }
                open_par -= 1;
            }
            b'\\' => {
                escaped = true;
                continue;
            }
            _ => (),
        }
        ret.push(v[i]);
    }
    Ok((v.slice(idx..), ret))
}

// PDF 32000-1:2008 standard: 7.3.4.2 Literal Strings
named!(pdf_literal_string<&[u8], Vec<u8> >,
    delimited!(
        tag!("("),
        parse_literal_string,
        tag!(")")
    )
);

fn hdig_for_char(c: &u8) -> Option<u8> {
    // Adapted from https://codereview.stackexchange.com/a/201699
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

fn parse_hex_string(v: Vec<&[u8]>) -> Vec<u8> {
    // Adapted from https://codereview.stackexchange.com/a/201699
    let mut hex_bytes = v.iter().map(|digits| digits.iter().filter_map(|c| hdig_for_char(c))).flatten();

    let mut bytes = Vec::new();
    while let (Some(hi), lo) = (hex_bytes.next(), hex_bytes.next()) {
        bytes.push(match lo {
            Some(l) => (hi << 4) | l,
            None => (hi << 4) | 0, // At the end of PDF hex strings, the low byte is optional.
        })
    }
    bytes
}

// PDF 32000-1:2008 standard: 7.3.4.3 Hexadecimal Strings
named!(pdf_hex_string<&[u8], Vec<u8> >,
    map!(
        delimited!(
            tag!("<"),
            fold_many0!(
                sep!(
                    pdf_separator,
                    hex_digit
                ),
                Vec::new(),
                |mut acc: Vec<_>, item| {
                    acc.push(item);
                    acc
                }
            ),
            preceded!(
                pdf_separator,
                tag!(">")
            )
        ),
        parse_hex_string
    )
);

named!(pdf_string<&[u8], Vec<u8> >,
    alt!(
        pdf_literal_string | pdf_hex_string
    )
);

fn parse_name(v: &[u8]) -> IResult<&[u8], PdfName> {
    // TODO: Needs improvement.
    let mut ret = PdfName::new();

    let len = v.len();
    let mut i = 0;
    while i != len {
        if v[i] == b'#' {
            if len - i < 3 {
                return Err(Err::Incomplete(Needed::Size(3 - (len - i))));
            }

            if !is_hex_digit(v[i + 1]) {
                // TODO: Replace with a better error code?
                return Err(Err::Incomplete(Needed::Size(2)));
            }

            if !is_hex_digit(v[i + 2]) {
                // TODO: Replace with a better error code?
                return Err(Err::Incomplete(Needed::Size(1)));
            }

            // FIXME: Assumes valid input for hex characters.
            let c = (hdig_for_char(&v[i + 1]).unwrap() << 4) | hdig_for_char(&v[i + 2]).unwrap();
            i += 2;
            ret.push(c);
        } else if is_whitespace(v[i])
            || v[i] == b'%'
            || v[i] == b'/'
            || v[i] == b'['
            || v[i] == b'('
            || v[i] == b'<'
            || v[i] == b']'
            || v[i] == b'>'
        {
            break;
        } else {
            ret.push(v[i]);
        }

        i += 1;
    }
    Ok((v.slice(i..), ret))
}

// PDF 32000-1:2008 standard: 7.3.5 Name Objects
named!(pdf_name<&[u8], PdfName>,
    do_parse!(
        name: preceded!(
            tag!("/"),
            parse_name
        ) >>
        (name.to_vec())
    )
);

// PDF 32000-1:2008 standard: 7.3.6 Array Objects
named!(pdf_array<&[u8], PdfArray>,
    // FIXME: Can't parse arrays with a Name at the end without a space between it and the closing
    // bracket. Bug in the name parser.
    do_parse!(
        tag!("[") >>
        opt!( pdf_separator ) >>
        array: many0!(
            do_parse!(
                object: pdf_object >>
                opt!( pdf_separator ) >>
                (object)
            )
        ) >>
        opt!( pdf_separator ) >>
        tag!("]") >>
        (array)
    )
);

fn tuples_to_pdf_dict(tuples: Vec<(PdfName, PdfObject)>) -> PdfDictionary {
    let mut dict = PdfDictionary::new();
    for (key, value) in tuples {
        dict.insert(key, value);
    }
    dict
}

// PDF 32000-1:2008 standard: 7.3.7 Dictionary Objects
named!(pdf_dictionary<&[u8], PdfDictionary>,
    do_parse!(
        tag!("<<") >>
        opt!( pdf_separator ) >>
        tuples: many0!(
            tuple!(
                do_parse!(
                    key: pdf_name >>
                    opt!( pdf_separator ) >>
                    (key)
                ),
                do_parse!(
                    value: pdf_object >>
                    opt!( pdf_separator ) >>
                    (value)
                )
            )
        ) >>
        opt!( pdf_separator ) >>
        tag!(">>") >>
        (tuples_to_pdf_dict(tuples))
    )
);

// PDF 32000-1:2008 standard: 7.3.8 Stream Objects
named!(pdf_stream<&[u8], PdfStream>,
    do_parse!(
        stream_dictionary: pdf_dictionary >>
        opt!( pdf_separator ) >>
        tag!( "stream" ) >>
        eol >> // CRLF or LF only.
        data: alt_complete!(
            // FIXME: This is a huge hack.
            take_until!("\r\nendstream") |
            take_until!("\nendstream") |
            take_until!("endstream")
        ) >>
        opt!( eol ) >> // "There should be an end-of-line marker after the data and before endstream;"
        tag!( "endstream" ) >>
        (PdfStream{dictionary: stream_dictionary, data: data.to_vec()})
    )
);

// PDF 32000-1:2008 standard: 7.3.9 Null Object
named!(pdf_null, tag!("null"));

named!(pdf_direct_object<&[u8], PdfDirectObject>,
    do_parse!(
        object: alt!(
            pdf_bool        => { |r:          bool| PdfDirectObject::PdfBool(r)       } |
            pdf_number      => { |r:     PdfNumber| PdfDirectObject::PdfNumber(r)     } |
            pdf_string      => { |r:       Vec<u8>| PdfDirectObject::PdfString(r)     } |
            pdf_name        => { |r:       PdfName| PdfDirectObject::PdfName(r)       } |
            pdf_array       => { |r:      PdfArray| PdfDirectObject::PdfArray(r)      } |
            pdf_stream      => { |r:     PdfStream| PdfDirectObject::PdfStream(r)     } |
            pdf_dictionary  => { |r: PdfDictionary| PdfDirectObject::PdfDictionary(r) } |
            pdf_null        => { |_|                PdfDirectObject::PdfNull()        }
        ) >>
        (object)
    )
);

// PDF 32000-1:2008 standard: 7.3.10 Indirect Objects
named!(pdf_indirect_object<&[u8], PdfIndirectObject>,
    do_parse!(
        obj_num: flat_map!(digit, parse_to!(u64)) >>
        pdf_separator >>
        gen_num: flat_map!(digit, parse_to!(u16)) >>
        pdf_separator >>
        tag!("obj") >>
        opt!( pdf_separator ) >>
        object: pdf_direct_object >>
        opt!( pdf_separator ) >>
        tag!("endobj") >>
        (PdfIndirectObject{obj_num, gen_num, object})
    )
);

named!(pdf_indirect_object_reference<&[u8], PdfIndirectObjectReference>,
    do_parse!(
        obj_num: flat_map!(digit, parse_to!(u64)) >>
        pdf_separator >>
        gen_num: flat_map!(digit, parse_to!(u16)) >>
        pdf_separator >>
        tag!("R") >>
        (PdfIndirectObjectReference{obj_num, gen_num})
    )
);

named!(pdf_object<&[u8], PdfObject>,
    do_parse!(
        object: alt!(
            pdf_indirect_object            => { |r:          PdfIndirectObject| PdfObject::PdfIndirectObject(r)          } |
            pdf_indirect_object_reference  => { |r: PdfIndirectObjectReference| PdfObject::PdfIndirectObjectReference(r) } |
            pdf_direct_object              => { |r:            PdfDirectObject| PdfObject::PdfDirectObject(r)            }
        ) >>
        (object)
    )
);

pub fn version_to_pdfversion(v: &[u8]) -> PdfVersion {
    match &v[0..3] {
        b"1.0" => PdfVersion::V1P0,
        b"1.1" => PdfVersion::V1P1,
        b"1.2" => PdfVersion::V1P2,
        b"1.3" => PdfVersion::V1P3,
        b"1.4" => PdfVersion::V1P4,
        b"1.5" => PdfVersion::V1P5,
        b"1.6" => PdfVersion::V1P6,
        b"1.7" => PdfVersion::V1P7,
        _ => PdfVersion::UNKNOWN,
    }
}

pub fn pdfversion_to_str(v: PdfVersion) -> &'static str {
    match v {
        PdfVersion::V1P0 => "1.0",
        PdfVersion::V1P1 => "1.1",
        PdfVersion::V1P2 => "1.2",
        PdfVersion::V1P3 => "1.3",
        PdfVersion::V1P4 => "1.4",
        PdfVersion::V1P5 => "1.5",
        PdfVersion::V1P6 => "1.6",
        PdfVersion::V1P7 => "1.7",
        _ => "Unknown",
    }
}

named!(pdf_version<&[u8], PdfVersion>,
    preceded!(
        tag!("%PDF-"),
        map!(
            recognize!(
                tuple!( digit, char!('.'), digit )
            ),
            version_to_pdfversion
        )
    )
);

named!(pdf_xrt_subsection_entry<&[u8], PdfXrtSubsectionEntry>,
    do_parse!(
        offset_or_obj_num: flat_map!(digit, parse_to!(u64)) >>
        char!(' ') >>
        gen: flat_map!(digit, parse_to!(u16)) >>
        char!(' ') >>
        status: alt!(
            char!('n') |
            char!('f')
        ) >>
        alt!(
            tag!(" \r") |
            tag!(" \n") |
            tag!("\r\n")
        ) >>
        (
            match status {
                'n' => PdfXrtSubsectionEntry::InUseObject(PdfXrtInUseObject{offset: offset_or_obj_num, gen}),
                'f' => PdfXrtSubsectionEntry::FreeObject(PdfXrtFreeObject{obj_num: offset_or_obj_num, gen}),
                _ => PdfXrtSubsectionEntry::FreeObject(PdfXrtFreeObject{obj_num: 0, gen: 0}),
            }
        )
    )
);

named!(pdf_xrt_subsection<&[u8], PdfXrtSubsection>,
    do_parse!(
        opt!( pdf_separator ) >>
        first_obj_num: flat_map!(digit, parse_to!(u64)) >>
        char!(' ') >>
        num_entries: flat_map!(digit, parse_to!(u64)) >>
        pdf_separator >>
        entries: many1!(
            pdf_xrt_subsection_entry
        ) >>
        (PdfXrtSubsection{first_obj_num, num_entries, entries})
    )
);

named!(pdf_xrt_section<&[u8], PdfXrtSection>,
    do_parse!(
        tag!( "xref" ) >>
        pdf_separator >>
        subsections: many1!(
            pdf_xrt_subsection
        ) >>
        (PdfXrtSection{subsections})
    )
);

named!(pdf_xrt<&[u8], PdfXrt>,
    do_parse!(
        sections: many1!(
            pdf_xrt_section
        ) >>
        (PdfXrt{sections})
    )
);

named!(pdf_trailer<&[u8], PdfTrailer>,
    do_parse!(
        tag!( "trailer" ) >>
        opt!( pdf_separator ) >>
        dictionary: pdf_dictionary >>
        opt!( pdf_separator ) >>
        tag!( "startxref" ) >>
        pdf_eol >>
        startxref: flat_map!(digit, parse_to!(u64)) >>
        pdf_eol >>
        tag!( "%%EOF" ) >>
        (PdfTrailer{dictionary, startxref})
    )
);

named!(pdf_elements<&[u8], Vec<PdfElement> >,
    many0!(
        alt!(
            pdf_comment         => { |r:        PdfComment| PdfElement::PdfComment(r)        } |
            pdf_whitespace      => { |r:     PdfWhitespace| PdfElement::PdfWhitespace(r)     } |
            pdf_indirect_object => { |r: PdfIndirectObject| PdfElement::PdfIndirectObject(r) }
        )
    )
);

/*
named!(pub parse_pdf<&[u8], PdfFile>,
    do_parse!(
        version: pdf_version >>
        opt!( pdf_separator ) >>
        objects: many0!(
            do_parse!(
                object: pdf_indirect_object >>
                opt!( pdf_separator ) >>
                (object)
            )
        ) >>
        opt!( pdf_separator ) >>
        xrt: pdf_xrt >>
        opt!( pdf_separator ) >>
        trailer: pdf_trailer >>
        (PdfFile{header: PdfHeader{version}, body: PdfBody{objects}, xrt, trailer})
    )
);
*/

fn find_u8_slice(input: &[u8], pattern: &[u8]) -> Option<usize> {
    let win_size = pattern.len();
    for (i, window) in input.windows(win_size).enumerate() {
        if window == pattern {
            return Some(i);
        }
    }
    None
}

fn rfind_u8_slice(input: &[u8], pattern: &[u8]) -> Option<usize> {
    let win_size = pattern.len();
    let input_len = input.len();
    for (i, window) in input.windows(win_size).rev().enumerate() {
        if window == pattern {
            return Some(input_len - i - win_size);
        }
    }
    None
}

fn get_eof_index(input: &[u8]) -> Option<usize> {
    rfind_u8_slice(input, &b"%%EOF"[..])
}

pub fn parse_pdf(input: &[u8]) -> IResult<&[u8], PdfFile> {
    // Read the header.
    let version = match pdf_version(input) {
        Ok(v) => v.1,
        // FIXME: Replace with real error.
        Err(_) => return Err(Err::Incomplete(Needed::Size(999900))),
    };
    let header = PdfHeader { version };

    // Find the end of the file.
    let eof_index = match get_eof_index(input) {
        Some(i) => i,
        // FIXME: Replace with real error.
        None => return Err(Err::Incomplete(Needed::Size(999901))),
    };

    // Find the start of the trailer by trial-and-error, since there's it's
    // possible for the trailer dictionary to contain the "trailer" keyword.
    // TODO: Find some better way to do this search loop.
    let mut trailer_option: Option<PdfTrailer> = None;
    let mut trailer_index = eof_index; // Start at the PDF EOF.
    while trailer_option.is_none() {
        // Get a possible index of the trailer.
        trailer_index = match rfind_u8_slice(&input[..trailer_index], &b"trailer"[..]) {
            Some(index) => index,
            None => {
                // TODO: Maybe print an error message here?
                eprintln!("Error: Missing trailer.");
                break;
            }
        };

        // Try parsing the trailer.
        let trailer = match pdf_trailer(&input[trailer_index..]) {
            Ok(t) => t.1,
            Err(_) => continue,
        };

        // Found the trailer.
        trailer_option = Some(trailer);
    }
    let trailer = match trailer_option {
        Some(t) => t,
        // FIXME: Replace with real error.
        None => return Err(Err::Incomplete(Needed::Size(999902))),
    };

    // TODO: Do this search in a loop with fuzzy matching of the startxref
    // offset, and log an INFO message if it's not in the expected location.
    let xrt_index = match usize::try_from((&trailer).startxref) {
        Ok(idx) => idx,
        Err(_) => return Err(Err::Incomplete(Needed::Size(999903))),
    };
    let xrt = match pdf_xrt(&input[xrt_index..]) {
        Ok(xrt) => xrt.1,
        Err(err) => {
            eprintln!("Error: {:?}", err);
            eprintln!(
                "Warning: Failed to parse XRT at {}, performing fuzzy search.",
                xrt_index
            );
            match rfind_u8_slice(&input[..xrt_index], &b"xref"[..]) {
                Some(offset) => match pdf_xrt(&input[xrt_index + offset..]) {
                    Ok(xrt) => {
                        eprintln!("Info: XRT found at {}.", xrt_index + offset);
                        xrt.1
                    }
                    Err(_) => {
                        eprintln!("Error: Failed to parse XRT at {}.", xrt_index + offset);
                        // FIXME: Replace with real error.
                        return Err(Err::Incomplete(Needed::Size(9999031)));
                    }
                },
                None => {
                    match find_u8_slice(&input[xrt_index..trailer_index], &b"xref"[..]) {
                        Some(offset) => match pdf_xrt(&input[xrt_index + offset..]) {
                            Ok(xrt) => {
                                eprintln!("Info: XRT found at {}.", xrt_index + offset);
                                xrt.1
                            }
                            Err(_) => {
                                eprintln!("Error: Failed to parse XRT at {}.", xrt_index + offset);
                                // FIXME: Replace with real error.
                                return Err(Err::Incomplete(Needed::Size(9999032)));
                            }
                        },
                        None => {
                            eprintln!("Error: Missing XRT.");
                            // FIXME: Replace with real error.
                            return Err(Err::Incomplete(Needed::Size(9999033)));
                        }
                    }
                }
            }
        }
    };

    // Loop through the in-use objects in the XRT and add them to the body.
    let mut objects: Vec<PdfIndirectObject> = vec![];
    for section in &xrt.sections {
        for subsection in &section.subsections {
            for entry in &subsection.entries {
                match entry {
                    PdfXrtSubsectionEntry::InUseObject(in_use_object) => {
                        // FIXME: Check for usize overflow/underflow.
                        match pdf_indirect_object(&input[((&in_use_object).offset as usize)..]) {
                            Ok(object) => objects.push(object.1),
                            // FIXME: Replace with real error.
                            Err(_) => return Err(Err::Incomplete(Needed::Size(999904))),
                        }
                    }
                    _ => (),
                }
            }
        }
    }
    let body = PdfBody { objects };

    Ok((
        &input[eof_index + 5..],
        PdfFile {
            header,
            body,
            xrt,
            trailer,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    //use std::str::from_utf8;

    //const EMPTY: &'static [u8] = b"";

    // Based on code from here: https://stackoverflow.com/a/27582993
    macro_rules! pdf_dict(
        { $($key:expr => $value:expr),+ } => {
            {
                let mut m = PdfDictionary::new();
                $(
                    m.insert($key, $value);
                )+
                m
            }
         };
    );

    #[test]
    fn pdf_eol_ok_test() {
        let testcase1 = &b"\r\n;"[..];
        assert_eq!(pdf_eol(testcase1), Ok((&b";"[..], &b"\r\n"[..])));
        let testcase2 = &b"\n;"[..];
        assert_eq!(pdf_eol(testcase2), Ok((&b";"[..], &b"\n"[..])));
        let testcase3 = &b"\r;"[..];
        assert_eq!(pdf_eol(testcase3), Ok((&b";"[..], &b"\r"[..])));

        // Make sure CRLF is treated as a single EOL token.
        named!(multi_eol<&[u8], Vec<&[u8]> >, many1!( pdf_eol ) );
        let testcase4 = &b"\n\r\r\n\r\r\n\n\n\n\r\r\r\r\n\r\n\r;"[..];
        let test4 = multi_eol(testcase4);
        assert!(test4.is_ok());
        let res4 = test4.unwrap();
        assert_eq!(res4.0, &b";"[..]);
        assert_eq!(res4.1.len(), 14);
    }

    #[test]
    fn pdf_whitespace_ok_test() {
        assert_eq!(
            pdf_whitespace(&b"      ;"[..]),
            Ok((
                &b";"[..],
                PdfWhitespace {
                    whitespace: b"      "[..].to_vec()
                }
            ))
        );
        assert_eq!(
            pdf_whitespace(&b"  \0\n\r    ;"[..]),
            Ok((
                &b";"[..],
                PdfWhitespace {
                    whitespace: b"  \0\n\r    "[..].to_vec()
                }
            ))
        );
        assert_eq!(
            pdf_whitespace(&b"\n\n\n\n\r\t\0\x0c;"[..]),
            Ok((
                &b";"[..],
                PdfWhitespace {
                    whitespace: b"\n\n\n\n\r\t\0\x0c"[..].to_vec()
                }
            ))
        );
        assert_eq!(
            pdf_whitespace(&b"\n\r\r\n\r\r\n\n\n\n\r\r\r\r\n\r\n\r;"[..]),
            Ok((
                &b";"[..],
                PdfWhitespace {
                    whitespace: b"\n\r\r\n\r\r\n\n\n\n\r\r\r\r\n\r\n\r"[..].to_vec()
                }
            ))
        );
    }

    #[test]
    fn pdf_comment_ok_test() {
        // Empty comments
        assert_eq!(
            pdf_comment(&b"%\n;"[..]),
            Ok((
                &b"\n;"[..],
                PdfComment {
                    comment: b""[..].to_vec()
                }
            ))
        );
        assert_eq!(
            pdf_comment(&b"%\r;"[..]),
            Ok((
                &b"\r;"[..],
                PdfComment {
                    comment: b""[..].to_vec()
                }
            ))
        );
        assert_eq!(
            pdf_comment(&b"%\r\n;"[..]),
            Ok((
                &b"\r\n;"[..],
                PdfComment {
                    comment: b""[..].to_vec()
                }
            ))
        );

        // PDF header
        assert_eq!(
            pdf_comment(&b"%PDF-1.1\n;"[..]),
            Ok((
                &b"\n;"[..],
                PdfComment {
                    comment: b"PDF-1.1"[..].to_vec()
                }
            ))
        );

        // High-bit characters
        assert_eq!(
            pdf_comment(&b"%\xc2\xa5\xc2\xb1\xc3\xab\n;"[..]),
            Ok((
                &b"\n;"[..],
                PdfComment {
                    comment: b"\xc2\xa5\xc2\xb1\xc3\xab"[..].to_vec()
                }
            ))
        );

        // Example comment
        assert_eq!(
            pdf_comment(&b"% comment (/%) blah blah blah\n;"[..]),
            Ok((
                &b"\n;"[..],
                PdfComment {
                    comment: b" comment (/%) blah blah blah"[..].to_vec()
                }
            ))
        );
    }

    #[test]
    fn pdf_book_ok_test() {
        assert_eq!(pdf_bool(&b"true;"[..]), Ok((&b";"[..], true)));
        assert_eq!(pdf_bool(&b"false;"[..]), Ok((&b";"[..], false)));
    }

    #[test]
    fn pdf_integer_ok_test() {
        assert_eq!(pdf_integer(&b"123;"[..]), Ok((&b";"[..], 123)));
        assert_eq!(pdf_integer(&b"43445;"[..]), Ok((&b";"[..], 43445)));
        assert_eq!(pdf_integer(&b"+17;"[..]), Ok((&b";"[..], 17)));
        assert_eq!(pdf_integer(&b"-98;"[..]), Ok((&b";"[..], -98)));
        assert_eq!(pdf_integer(&b"0;"[..]), Ok((&b";"[..], 0)));
    }

    #[test]
    fn pdf_real_ok_test() {
        assert_eq!(pdf_real(&b"34.5;"[..]), Ok((&b";"[..], 34.5)));
        assert_eq!(pdf_real(&b"-3.62;"[..]), Ok((&b";"[..], -3.62)));
        assert_eq!(pdf_real(&b"+123.6;"[..]), Ok((&b";"[..], 123.6)));
        assert_eq!(pdf_real(&b"4.;"[..]), Ok((&b";"[..], 4.0)));
        assert_eq!(pdf_real(&b"-.002;"[..]), Ok((&b";"[..], -0.002)));
        assert_eq!(pdf_real(&b"0.0;"[..]), Ok((&b";"[..], 0.0)));
    }

    #[test]
    fn pdf_number_ok_test() {
        // Integer
        assert_eq!(
            pdf_number(&b"123;"[..]),
            Ok((&b";"[..], PdfNumber::PdfInteger(123)))
        );
        assert_eq!(
            pdf_number(&b"43445;"[..]),
            Ok((&b";"[..], PdfNumber::PdfInteger(43445)))
        );
        assert_eq!(
            pdf_number(&b"+17;"[..]),
            Ok((&b";"[..], PdfNumber::PdfInteger(17)))
        );
        assert_eq!(
            pdf_number(&b"-98;"[..]),
            Ok((&b";"[..], PdfNumber::PdfInteger(-98)))
        );
        assert_eq!(
            pdf_number(&b"0;"[..]),
            Ok((&b";"[..], PdfNumber::PdfInteger(0)))
        );

        // Real
        assert_eq!(
            pdf_number(&b"34.5;"[..]),
            Ok((&b";"[..], PdfNumber::PdfReal(34.5)))
        );
        assert_eq!(
            pdf_number(&b"-3.62;"[..]),
            Ok((&b";"[..], PdfNumber::PdfReal(-3.62)))
        );
        assert_eq!(
            pdf_number(&b"+123.6;"[..]),
            Ok((&b";"[..], PdfNumber::PdfReal(123.6)))
        );
        assert_eq!(
            pdf_number(&b"4.;"[..]),
            Ok((&b";"[..], PdfNumber::PdfReal(4.0)))
        );
        assert_eq!(
            pdf_number(&b"-.002;"[..]),
            Ok((&b";"[..], PdfNumber::PdfReal(-0.002)))
        );
        assert_eq!(
            pdf_number(&b"0.0;"[..]),
            Ok((&b";"[..], PdfNumber::PdfReal(0.0)))
        );
    }

    #[test]
    fn pdf_string_ok_test() {
        // Literal Strings
        // Example 1
        assert_eq!(
            pdf_literal_string(&b"(This is a string);"[..]),
            Ok((&b";"[..], b"This is a string"[..].to_vec()))
        );
        assert_eq!(
            pdf_literal_string(&b"(Strings may contain newlines\nand such.);"[..]),
            Ok((
                &b";"[..],
                b"Strings may contain newlines\nand such."[..].to_vec()
            ))
        );
        assert_eq!(pdf_string(&b"(Strings may contain balanced parentheses () and\nspecial characters (*!&}^% and so on).);"[..]), Ok((&b";"[..], b"Strings may contain balanced parentheses () and\nspecial characters (*!&}^% and so on)."[..].to_vec())));
        assert_eq!(
            pdf_literal_string(&b"(The following is an empty string.);"[..]),
            Ok((&b";"[..], b"The following is an empty string."[..].to_vec()))
        );
        assert_eq!(
            pdf_literal_string(&b"();"[..]),
            Ok((&b";"[..], b""[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"(It has zero (0) length.);"[..]),
            Ok((&b";"[..], b"It has zero (0) length."[..].to_vec()))
        );

        // Example 2
        assert_eq!(
            pdf_string(&b"(These \\\ntwo strings \\\nare the same.);"[..]),
            Ok((&b";"[..], b"These two strings are the same."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"(These \\\rtwo strings \\\rare the same.);"[..]),
            Ok((&b";"[..], b"These two strings are the same."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"(These \\\r\ntwo strings \\\r\nare the same.);"[..]),
            Ok((&b";"[..], b"These two strings are the same."[..].to_vec()))
        );

        // Example 3
        assert_eq!(
            pdf_string(&b"(This string has an end-of-line at the end of it.\n);"[..]),
            Ok((
                &b";"[..],
                b"This string has an end-of-line at the end of it.\n"[..].to_vec()
            ))
        );
        assert_eq!(
            pdf_string(&b"(So does this one.\\n);"[..]),
            Ok((&b";"[..], b"So does this one.\n"[..].to_vec()))
        );

        // Example 4
        assert_eq!(
            pdf_string(&b"(This string contains \\245two octal characters\\307.);"[..]),
            Ok((
                &b";"[..],
                b"This string contains \xA5two octal characters\xC7."[..].to_vec()
            ))
        );
        // "high-order overflow shall be ignored"
        assert_eq!(
            pdf_string(&b"(This string contains \\645two octal characters\\707.);"[..]),
            Ok((
                &b";"[..],
                b"This string contains \xA5two octal characters\xC7."[..].to_vec()
            ))
        );

        // Example 5
        assert_eq!(
            pdf_string(&b"(\\0053);"[..]),
            Ok((&b";"[..], b"\x053"[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"(\\053);"[..]),
            Ok((&b";"[..], b"+"[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"(\\53);"[..]),
            Ok((&b";"[..], b"+"[..].to_vec()))
        );

        // Hexadecimal strings
        // Example 1
        assert_eq!(
            pdf_string(&b"<4E6F762073686D6F7A206B6120706F702E>;"[..]),
            Ok((&b";"[..], b"Nov shmoz ka pop."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"<4e6f762073686d6f7a206b6120706f702e>;"[..]),
            Ok((&b";"[..], b"Nov shmoz ka pop."[..].to_vec()))
        );

        // Example 2
        assert_eq!(
            pdf_string(&b"<901FA3>;"[..]),
            Ok((&b";"[..], b"\x90\x1F\xA3"[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"<901FA>;"[..]),
            Ok((&b";"[..], b"\x90\x1F\xA0"[..].to_vec()))
        );

        // Whitespace tests
        assert_eq!(
            pdf_string(&b"<4e 6f   76  2073     686d6f7a206b6120706f702e>;"[..]),
            Ok((&b";"[..], b"Nov shmoz ka pop."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"<4e 6f   76  2073     68\n6d6f7a206b6120706f702e>;"[..]),
            Ok((&b";"[..], b"Nov shmoz ka pop."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"< 4e 6f   76  2073     68\n6d6f7a206b6120706f702e>;"[..]),
            Ok((&b";"[..], b"Nov shmoz ka pop."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"< 4 e 6 f   76  2073     68\n6d6f7a206b6120706f702e>;"[..]),
            Ok((&b";"[..], b"Nov shmoz ka pop."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"< 4e 6%this is a comment 1234\r\nf   76  2073     68\n6d6f7a206b6120706f702e>;"[..]),
            Ok((&b";"[..], b"Nov shmoz ka pop."[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"< 9 0 1 F A >;"[..]),
            Ok((&b";"[..], b"\x90\x1F\xA0"[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"< 9 0 1\n F\n A >;"[..]),
            Ok((&b";"[..], b"\x90\x1F\xA0"[..].to_vec()))
        );
        assert_eq!(
            pdf_string(&b"<%comment123\n9%comment456\n 0 1 F A >;"[..]),
            Ok((&b";"[..], b"\x90\x1F\xA0"[..].to_vec()))
        );
        // FIXME: This doesn't work for some reason. Returns Ok((&b";"[..], b"\x1F\xA0"[..].to_vec()))
        //assert_eq!(
        //    pdf_string(&b"< %comment123\n9%comment456\n 0% 42 comment \r\n1  F%comment\n\r%comment 12345\n A >;"[..]),
        //    Ok((&b";"[..], b"\x90\x1F\xA0"[..].to_vec()))
        //);

        // Zero-length hexadecimal strings with whitespace.
        assert_eq!(pdf_string(&b"<>;"[..]), Ok((&b";"[..], b""[..].to_vec())));
        assert_eq!(pdf_string(&b"<   >;"[..]), Ok((&b";"[..], b""[..].to_vec())));
        assert_eq!(pdf_string(&b"<%comment\n>;"[..]), Ok((&b";"[..], b""[..].to_vec())));
        assert_eq!(pdf_string(&b"< %comment\n >;"[..]), Ok((&b";"[..], b""[..].to_vec())));
        assert_eq!(
            pdf_string(&b"< %comment123\n%comment456\n % 42 comment \r\n  %comment\n\r%comment 12345\n  >;"[..]),
            Ok((&b";"[..], b""[..].to_vec()))
        );
    }

    #[test]
    fn pdf_name_ok_test() {
        assert_eq!(
            pdf_name(&b"/Name1 "[..]),
            Ok((&b" "[..], b"Name1"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/ASomewhatLongerName "[..]),
            Ok((&b" "[..], b"ASomewhatLongerName"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/A;Name_With-Various***Characters? "[..]),
            Ok((&b" "[..], b"A;Name_With-Various***Characters?"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/1.2 "[..]),
            Ok((&b" "[..], b"1.2"[..].to_vec()))
        );
        assert_eq!(pdf_name(&b"/$$ "[..]), Ok((&b" "[..], b"$$"[..].to_vec())));
        assert_eq!(
            pdf_name(&b"/@pattern "[..]),
            Ok((&b" "[..], b"@pattern"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/.notdef "[..]),
            Ok((&b" "[..], b".notdef"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/Lime#20Green "[..]),
            Ok((&b" "[..], b"Lime Green"[..].to_vec()))
        ); // Example was "/lime#20Green" but I'm pretty sure they meant "/Lime#20Green".
        assert_eq!(
            pdf_name(&b"/paired#28#29parentheses "[..]),
            Ok((&b" "[..], b"paired()parentheses"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/The_Key_of_F#23_Minor "[..]),
            Ok((&b" "[..], b"The_Key_of_F#_Minor"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/A#42 "[..]),
            Ok((&b" "[..], b"AB"[..].to_vec()))
        );
        assert_eq!(
            pdf_name(&b"/A_Name/Another_Name"[..]),
            Ok((&b"/Another_Name"[..], b"A_Name"[..].to_vec()))
        );
    }

    #[test]
    fn pdf_name_err_test() {
        // TODO: Check for specific error types.
        assert!(pdf_name(&b"/Lime# "[..]).is_err()); // Incomplete, need 2.
        assert!(pdf_name(&b"/Lime#2 "[..]).is_err()); // Incomplete, need 1.
        assert!(pdf_name(&b"/Lime#2X "[..]).is_err()); // Incomplete, need 1.
        assert!(pdf_name(&b"/Lime#X0 "[..]).is_err()); // Incomplete, need 2.
    }

    #[test]
    fn pdf_array_ok_test() {
        assert_eq!(pdf_array(&b"[];"[..]), Ok((&b";"[..], PdfArray::new())));
        assert_eq!(
            pdf_array(&b"[549 3.14 false (Ralph) /SomeName];"[..]),
            Ok((
                &b";"[..],
                vec![
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(
                        549
                    ))),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfReal(
                        3.14
                    ))),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfBool(false)),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"Ralph"[..].to_vec())),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfName(b"SomeName"[..].to_vec()))
                ]
            ))
        );
        assert_eq!(
            pdf_array(&b"[549 3.14 false (Ralph) /SomeName ];"[..]),
            Ok((
                &b";"[..],
                vec![
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(
                        549
                    ))),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfReal(
                        3.14
                    ))),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfBool(false)),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"Ralph"[..].to_vec())),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfName(b"SomeName"[..].to_vec()))
                ]
            ))
        );
        assert_eq!(
            pdf_array(&b"[ 549 3.14 false (Ralph) /SomeName ];"[..]),
            Ok((
                &b";"[..],
                vec![
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(
                        549
                    ))),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfReal(
                        3.14
                    ))),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfBool(false)),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"Ralph"[..].to_vec())),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfName(b"SomeName"[..].to_vec()))
                ]
            ))
        );
        assert_eq!(
            pdf_array(&b"[ <666f6f> <626172> ];"[..]),
            Ok((
                &b";"[..],
                vec![
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"foo"[..].to_vec())),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"bar"[..].to_vec()))
                ]
            ))
        );
        assert_eq!(
            pdf_array(&b"[<666f6f> <626172>];"[..]),
            Ok((
                &b";"[..],
                vec![
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"foo"[..].to_vec())),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"bar"[..].to_vec()))
                ]
            ))
        );
        assert_eq!(
            pdf_array(&b"[<666f6f><626172>];"[..]),
            Ok((
                &b";"[..],
                vec![
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"foo"[..].to_vec())),
                    PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"bar"[..].to_vec()))
                ]
            ))
        );
    }

    #[test]
    fn pdf_dictionary_ok_test() {
        // Empty dictionary.
        assert_eq!(
            pdf_dictionary(&b"<<>>;"[..]),
            Ok((&b";"[..], PdfDictionary::new()))
        );

        // Example
        assert_eq!(pdf_dictionary(&b"<< /Type /Example\n   /Subtype /DictionaryExample\n   /Version 0.01\n   /IntegerItem 12\n   /StringItem (a string)\n   /Subdictionary << /Item1 0.4\n      /Item2 true\n      /LastItem (not!)\n      /VeryLastItem (OK)\n   >>\n>>;"[..]), Ok((&b";"[..], pdf_dict!(
            b"Type"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfName(b"Example"[..].to_vec())),
            b"Subtype"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfName(b"DictionaryExample"[..].to_vec())),
            b"Version"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfReal(0.01))),
            b"IntegerItem"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(12))),
            b"StringItem"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"a string"[..].to_vec())),
            b"Subdictionary"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfDictionary(pdf_dict!(
                b"Item1"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfReal(0.4))),
                b"Item2"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfBool(true)),
                b"LastItem"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"not!"[..].to_vec())),
                b"VeryLastItem"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfString(b"OK"[..].to_vec()))
            )))
        ))));

        // Handle Name Object next to value objects.
        assert_eq!(
            pdf_dictionary(&b"<</ID[]>>;"[..]),
            Ok((
                &b";"[..],
                pdf_dict!(
                    b"ID"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfArray(vec![]))
                )
            ))
        );
        assert_eq!(
            pdf_dictionary(&b"<</ID()>>;"[..]),
            Ok((
                &b";"[..],
                pdf_dict!(
                    b"ID"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfString(vec![]))
                )
            ))
        );
        assert_eq!(
            pdf_dictionary(&b"<</ID/Foo>>;"[..]),
            Ok((
                &b";"[..],
                pdf_dict!(
                    b"ID"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfName(b"Foo"[..].to_vec()))
                )
            ))
        );
    }

    #[test]
    fn pdf_stream_ok_test() {
        // Streams are normally supposed to always be inside an indirect
        // object, but we test them here as direct objects.

        // Empty stream.
        let empty_stream = b"<</Length 0>>\nstream\nendstream;";
        let result = pdf_stream(&empty_stream[..]);
        assert_eq!(
            result,
            Ok((
                &b";"[..],
                PdfStream {
                    dictionary: pdf_dict!(
                        b"Length"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(0)))
                    ),
                    data: vec![],
                }
            ))
        );
        let parsed_stream = result.unwrap().1;
        assert_eq!(
            parsed_stream
                .dictionary
                .get(&b"Length"[..].to_vec())
                .unwrap(),
            &PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(
                parsed_stream.data.len() as i32
            )))
        );
    }

    #[test]
    fn pdf_direct_object_ok_test() {
        assert_eq!(
            pdf_direct_object(&b"(This is a string);"[..]),
            Ok((
                &b";"[..],
                PdfDirectObject::PdfString(b"This is a string"[..].to_vec())
            ))
        );
    }

    #[test]
    fn pdf_indirect_object_ok_test() {
        // Example 1
        assert_eq!(
            pdf_indirect_object(&b"12 0 obj\n   (Brillig)\nendobj;"[..]),
            Ok((
                &b";"[..],
                PdfIndirectObject {
                    obj_num: 12,
                    gen_num: 0,
                    object: PdfDirectObject::PdfString(b"Brillig".to_vec())
                }
            ))
        );

        // Example 3
        assert_eq!(pdf_indirect_object(&b"7 0 obj\n   << /Length 8 0 R >>\nstream\n\tBT\n    /F1 12 Tf\n    72 712 Td\n    (A stream with an indirect length) Tj\n\tET\nendstream\nendobj;"[..]), Ok((&b";"[..],
            PdfIndirectObject{
                obj_num: 7,
                gen_num: 0,
                object: PdfDirectObject::PdfStream(
                    PdfStream{
                        dictionary: pdf_dict!(
                            b"Length"[..].to_vec() => PdfObject::PdfIndirectObjectReference(PdfIndirectObjectReference{obj_num: 8, gen_num: 0})
                        ),
                        data: b"\tBT\n    /F1 12 Tf\n    72 712 Td\n    (A stream with an indirect length) Tj\n\tET"[..].to_vec()
                    }
                )
            }
        )));
        assert_eq!(
            pdf_indirect_object(&b"8 0 obj\n   77\nendobj;"[..]),
            Ok((
                &b";"[..],
                PdfIndirectObject {
                    obj_num: 8,
                    gen_num: 0,
                    object: PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(77))
                }
            ))
        );

        // Minimal PDF
        assert_eq!(
            pdf_indirect_object(
                &b"1 0 obj\n  << /Type /Catalog\n     /Pages 2 0 R\n  >>\nendobj;"[..]
            ),
            Ok((
                &b";"[..],
                PdfIndirectObject {
                    obj_num: 1,
                    gen_num: 0,
                    object: PdfDirectObject::PdfDictionary(pdf_dict!(
                        b"Type"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfName(b"Catalog"[..].to_vec())),
                        b"Pages"[..].to_vec() => PdfObject::PdfIndirectObjectReference(PdfIndirectObjectReference{obj_num: 2, gen_num: 0})
                    ))
                }
            ))
        );
        assert_eq!(pdf_indirect_object(&b"4 0 obj\n  << /Length 55 >>\nstream\n  BT\n    /F1 18 Tf\n    0 0 Td\n    (Hello World) Tj\n  ET\nendstream\nendobj\n"[..]), Ok((&b"\n"[..],
            PdfIndirectObject{
                obj_num: 4,
                gen_num: 0,
                object: PdfDirectObject::PdfStream(
                    PdfStream{
                        dictionary: pdf_dict!(
                            b"Length"[..].to_vec() => PdfObject::PdfDirectObject(PdfDirectObject::PdfNumber(PdfNumber::PdfInteger(55)))
                        ),
                        data: b"  BT\n    /F1 18 Tf\n    0 0 Td\n    (Hello World) Tj\n  ET"[..].to_vec()
                    }
                )
            }
        )));
    }

    #[test]
    fn pdf_indirect_object_reference_ok_test() {
        assert_eq!(
            pdf_indirect_object_reference(&b"1 0 R;"[..]),
            Ok((
                &b";"[..],
                PdfIndirectObjectReference {
                    obj_num: 1,
                    gen_num: 0
                }
            ))
        );
    }

    #[test]
    fn pdf_object_ok_test() {
        assert_eq!(
            pdf_object(&b"(This is a string);"[..]),
            Ok((
                &b";"[..],
                PdfObject::PdfDirectObject(PdfDirectObject::PdfString(
                    b"This is a string"[..].to_vec()
                ))
            ))
        );
        assert_eq!(
            pdf_object(&b"12 0 obj\n   (Brillig)\nendobj;"[..]),
            Ok((
                &b";"[..],
                PdfObject::PdfIndirectObject(PdfIndirectObject {
                    obj_num: 12,
                    gen_num: 0,
                    object: PdfDirectObject::PdfString(b"Brillig".to_vec())
                })
            ))
        );
        assert_eq!(
            pdf_object(&b"1 0 R;"[..]),
            Ok((
                &b";"[..],
                PdfObject::PdfIndirectObjectReference(PdfIndirectObjectReference {
                    obj_num: 1,
                    gen_num: 0
                })
            ))
        );
    }

    #[test]
    fn version_to_pdfversion_ok_test() {
        assert_eq!(version_to_pdfversion(&b"1.0"[..]), PdfVersion::V1P0);
        assert_eq!(version_to_pdfversion(&b"1.1"[..]), PdfVersion::V1P1);
        assert_eq!(version_to_pdfversion(&b"1.2"[..]), PdfVersion::V1P2);
        assert_eq!(version_to_pdfversion(&b"1.3"[..]), PdfVersion::V1P3);
        assert_eq!(version_to_pdfversion(&b"1.4"[..]), PdfVersion::V1P4);
        assert_eq!(version_to_pdfversion(&b"1.5"[..]), PdfVersion::V1P5);
        assert_eq!(version_to_pdfversion(&b"1.6"[..]), PdfVersion::V1P6);
        assert_eq!(version_to_pdfversion(&b"1.7"[..]), PdfVersion::V1P7);
    }

    #[test]
    fn pdf_version_ok_test() {
        assert_eq!(
            pdf_version(&b"%PDF-1.4\n"[..]),
            Ok((&b"\n"[..], PdfVersion::V1P4))
        );
    }

    #[test]
    fn pdf_xrt_ok_test() {
        assert_eq!(pdf_xrt(&b"xref\n0 6\n0000000003 65535 f \n0000000017 00000 n \n0000000081 00000 n \n0000000000 00007 f \n0000000331 00000 n \n0000000409 00000 n \n;"[..]), Ok((&b";"[..],
            PdfXrt{
                sections: vec![
                    PdfXrtSection{
                        subsections: vec![
                            PdfXrtSubsection{
                                first_obj_num: 0,
                                num_entries: 6,
                                entries: vec![
                                    PdfXrtSubsectionEntry::FreeObject(
                                        PdfXrtFreeObject{
                                            obj_num: 3,
                                            gen: 65535,
                                        }
                                    ),
                                    PdfXrtSubsectionEntry::InUseObject(
                                        PdfXrtInUseObject{
                                            offset: 17,
                                            gen: 0,
                                        }
                                    ),
                                    PdfXrtSubsectionEntry::InUseObject(
                                        PdfXrtInUseObject{
                                            offset: 81,
                                            gen: 0,
                                        }
                                    ),
                                    PdfXrtSubsectionEntry::FreeObject(
                                        PdfXrtFreeObject{
                                            obj_num: 0,
                                            gen: 7,
                                        }
                                    ),
                                    PdfXrtSubsectionEntry::InUseObject(
                                        PdfXrtInUseObject{
                                            offset: 331,
                                            gen: 0,
                                        }
                                    ),
                                    PdfXrtSubsectionEntry::InUseObject(
                                        PdfXrtInUseObject{
                                            offset: 409,
                                            gen: 0,
                                        }
                                    ),
                                ],
                            },
                        ],
                    },
                ],
            },
        )));
    }

    #[test]
    fn pdf_trailer_ok_test() {
        // Example
        assert_eq!(pdf_trailer(&b"trailer\n<< /Size 22\n/Root 2 0 R\n/Info 1 0 R\n/ID [\n<81b14aafa313db63dbd6f981e49f94f4>\n<81b14aafa313db63dbd6f981e49f94f4>\n]\n>>\nstartxref\n18799\n%%EOF\n"[..]), Ok((&b"\n"[..],
            PdfTrailer{
                dictionary: pdf_dict!(
                    b"Size"[..].to_vec() => PdfObject::PdfDirectObject(
                        PdfDirectObject::PdfNumber(
                            PdfNumber::PdfInteger(22)
                        )
                    ),
                    b"Root"[..].to_vec() => PdfObject::PdfIndirectObjectReference(
                        PdfIndirectObjectReference {
                            obj_num: 2,
                            gen_num: 0
                        }
                    ),
                    b"Info"[..].to_vec() => PdfObject::PdfIndirectObjectReference(
                        PdfIndirectObjectReference {
                            obj_num: 1,
                            gen_num: 0
                        }
                    ),
                    b"ID"[..].to_vec() => PdfObject::PdfDirectObject(
                        PdfDirectObject::PdfArray(
                            vec![
                                PdfObject::PdfDirectObject(
                                    PdfDirectObject::PdfString(vec![129, 177, 74, 175, 163, 19, 219, 99, 219, 214, 249, 129, 228, 159, 148, 244])
                                ),
                                PdfObject::PdfDirectObject(
                                    PdfDirectObject::PdfString(vec![129, 177, 74, 175, 163, 19, 219, 99, 219, 214, 249, 129, 228, 159, 148, 244])
                                )
                            ]
                        )
                    )
                ),
                startxref: 18799
            }
        )));
    }

    #[test]
    fn find_u8_slice_ok_test() {
        assert_eq!(find_u8_slice(&b""[..], &b"%%EOF"[..]), None);
        assert_eq!(find_u8_slice(&b"%EOF"[..], &b"%%EOF"[..]), None);
        assert_eq!(find_u8_slice(&b"%%EOF"[..], &b"%%EOF"[..]), Some(0));
        assert_eq!(find_u8_slice(&b"\n%%EOF"[..], &b"%%EOF"[..]), Some(1));
        assert_eq!(
            find_u8_slice(&b"%PDF-1.1\n%%EOF"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            find_u8_slice(&b"%PDF-1.1\n%%EOF\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            find_u8_slice(&b"%PDF-1.1\n%%EOF\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            find_u8_slice(&b"%PDF-1.1\n%%EOF\n\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            find_u8_slice(&b"%PDF-1.1\n%%EOF\n\n\n\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            find_u8_slice(&b"%PDF-1.1\n%%EOF\n\n\n\n\n\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
    }

    #[test]
    fn rfind_u8_slice_ok_test() {
        assert_eq!(rfind_u8_slice(&b""[..], &b"%%EOF"[..]), None);
        assert_eq!(rfind_u8_slice(&b"%EOF"[..], &b"%%EOF"[..]), None);
        assert_eq!(rfind_u8_slice(&b"%%EOF"[..], &b"%%EOF"[..]), Some(0));
        assert_eq!(
            rfind_u8_slice(&b"%PDF-1.1\n%%EOF"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            rfind_u8_slice(&b"%PDF-1.1\n%%EOF\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            rfind_u8_slice(&b"%PDF-1.1\n%%EOF\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            rfind_u8_slice(&b"%PDF-1.1\n%%EOF\n\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            rfind_u8_slice(&b"%PDF-1.1\n%%EOF\n\n\n\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
        assert_eq!(
            rfind_u8_slice(&b"%PDF-1.1\n%%EOF\n\n\n\n\n\n\n"[..], &b"%%EOF"[..]),
            Some(9)
        );
    }

    #[test]
    fn get_eof_index_ok_test() {
        assert_eq!(get_eof_index(&b""[..]), None);
        assert_eq!(get_eof_index(&b"%EOF"[..]), None);
        assert_eq!(get_eof_index(&b"%%EOF"[..]), Some(0));
        assert_eq!(get_eof_index(&b"%PDF-1.1\n%%EOF"[..]), Some(9));
        assert_eq!(get_eof_index(&b"%PDF-1.1\n%%EOF\n"[..]), Some(9));
        assert_eq!(get_eof_index(&b"%PDF-1.1\n%%EOF\n\n"[..]), Some(9));
        assert_eq!(get_eof_index(&b"%PDF-1.1\n%%EOF\n\n\n"[..]), Some(9));
        assert_eq!(get_eof_index(&b"%PDF-1.1\n%%EOF\n\n\n\n\n"[..]), Some(9));
        assert_eq!(
            get_eof_index(&b"%PDF-1.1\n%%EOF\n\n\n\n\n\n\n"[..]),
            Some(9)
        );
    }

    #[test]
    fn parse_pdf_ok_test() {
        let pdf = parse_pdf(&b"%PDF-1.1\n%\xc2\xa5\xc2\xb1\xc3\xab\n\n1 0 obj\n  << /Type /Catalog\n     /Pages 2 0 R\n  >>\nendobj\n\n2 0 obj\n  << /Type /Pages\n     /Kids [3 0 R]\n     /Count 1\n     /MediaBox [0 0 300 144]\n  >>\nendobj\n\n3 0 obj\n  <<  /Type /Page\n      /Parent 2 0 R\n      /Resources\n       << /Font\n           << /F1\n               << /Type /Font\n                  /Subtype /Type1\n                  /BaseFont /Times-Roman\n               >>\n           >>\n       >>\n      /Contents 4 0 R\n  >>\nendobj\n\n4 0 obj\n  << /Length 55 >>\nstream\n  BT\n    /F1 18 Tf\n    0 0 Td\n    (Hello World) Tj\n  ET\nendstream\nendobj\n\nxref\n0 5\n0000000000 65535 f \n0000000018 00000 n \n0000000077 00000 n \n0000000178 00000 n \n0000000457 00000 n \ntrailer\n  <<  /Root 1 0 R\n      /Size 5\n  >>\nstartxref\n565\n%%EOF\n"[..]);
        //println!("{:?}", &pdf);
        assert_eq!(
            pdf,
            Ok((
                &b"\n"[..],
                PdfFile {
                    header: PdfHeader {
                        version: PdfVersion::V1P1
                    },
                    body: PdfBody {
                        objects: vec![
                            PdfIndirectObject {
                                obj_num: 1,
                                gen_num: 0,
                                object: PdfDirectObject::PdfDictionary(pdf_dict!(
                                    b"Type"[..].to_vec() => PdfObject::PdfDirectObject(
                                        PdfDirectObject::PdfName(b"Catalog"[..].to_vec())
                                    ),
                                    b"Pages"[..].to_vec() => PdfObject::PdfIndirectObjectReference(
                                        PdfIndirectObjectReference {
                                            obj_num: 2,
                                            gen_num: 0,
                                        }
                                    )
                                ))
                            },
                            PdfIndirectObject {
                                obj_num: 2,
                                gen_num: 0,
                                object: PdfDirectObject::PdfDictionary(pdf_dict!(
                                    b"MediaBox"[..].to_vec() => PdfObject::PdfDirectObject(
                                        PdfDirectObject::PdfArray(
                                            vec![
                                                PdfObject::PdfDirectObject(
                                                    PdfDirectObject::PdfNumber(
                                                        PdfNumber::PdfInteger(0)
                                                    )
                                                ),
                                                PdfObject::PdfDirectObject(
                                                    PdfDirectObject::PdfNumber(
                                                        PdfNumber::PdfInteger(0)
                                                    )
                                                ),
                                                PdfObject::PdfDirectObject(
                                                    PdfDirectObject::PdfNumber(
                                                        PdfNumber::PdfInteger(300)
                                                    )
                                                ),
                                                PdfObject::PdfDirectObject(
                                                    PdfDirectObject::PdfNumber(
                                                        PdfNumber::PdfInteger(144)
                                                    )
                                                ),
                                            ],
                                        ),
                                    ),
                                    b"Kids"[..].to_vec() => PdfObject::PdfDirectObject(
                                        PdfDirectObject::PdfArray(
                                            vec![
                                                PdfObject::PdfIndirectObjectReference(
                                                    PdfIndirectObjectReference {
                                                        obj_num: 3,
                                                        gen_num: 0,
                                                    }
                                                )
                                            ]
                                        )
                                    ),
                                    b"Type"[..].to_vec() => PdfObject::PdfDirectObject(
                                        PdfDirectObject::PdfName(b"Pages"[..].to_vec())
                                    ),
                                    b"Count"[..].to_vec() => PdfObject::PdfDirectObject(
                                        PdfDirectObject::PdfNumber(
                                            PdfNumber::PdfInteger(1)
                                        )
                                    )
                                )),
                            },
                            PdfIndirectObject {
                                obj_num: 3,
                                gen_num: 0,
                                object: PdfDirectObject::PdfDictionary(pdf_dict!(
                                    b"Parent"[..].to_vec() => PdfObject::PdfIndirectObjectReference(
                                        PdfIndirectObjectReference {
                                            obj_num: 2,
                                            gen_num: 0
                                        }
                                    ),
                                    b"Type"[..].to_vec() => PdfObject::PdfDirectObject(
                                        PdfDirectObject::PdfName(b"Page"[..].to_vec())
                                    ),
                                    b"Resources"[..].to_vec() => PdfObject::PdfDirectObject(
                                        PdfDirectObject::PdfDictionary(
                                            pdf_dict!(
                                                b"Font"[..].to_vec() => PdfObject::PdfDirectObject(
                                                    PdfDirectObject::PdfDictionary(
                                                        pdf_dict!(
                                                            b"F1"[..].to_vec() => PdfObject::PdfDirectObject(
                                                                PdfDirectObject::PdfDictionary(
                                                                    pdf_dict!(
                                                                        b"Subtype"[..].to_vec() => PdfObject::PdfDirectObject(
                                                                            PdfDirectObject::PdfName(b"Type1"[..].to_vec())
                                                                        ),
                                                                        b"Type"[..].to_vec() => PdfObject::PdfDirectObject(
                                                                            PdfDirectObject::PdfName(b"Font"[..].to_vec())
                                                                        ),
                                                                        b"BaseFont"[..].to_vec() => PdfObject::PdfDirectObject(
                                                                            PdfDirectObject::PdfName(b"Times-Roman"[..].to_vec())
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    ),
                                    b"Contents"[..].to_vec() => PdfObject::PdfIndirectObjectReference(
                                        PdfIndirectObjectReference {
                                            obj_num: 4,
                                            gen_num: 0
                                        }
                                    )
                                ),),
                            },
                            PdfIndirectObject {
                                obj_num: 4,
                                gen_num: 0,
                                object: PdfDirectObject::PdfStream(PdfStream {
                                    dictionary: pdf_dict!(
                                        b"Length"[..].to_vec() => PdfObject::PdfDirectObject(
                                            PdfDirectObject::PdfNumber(
                                                PdfNumber::PdfInteger(55)
                                            )
                                        )
                                    ),
                                    data: vec![
                                        32, 32, 66, 84, 10, 32, 32, 32, 32, 47, 70, 49, 32, 49, 56,
                                        32, 84, 102, 10, 32, 32, 32, 32, 48, 32, 48, 32, 84, 100,
                                        10, 32, 32, 32, 32, 40, 72, 101, 108, 108, 111, 32, 87,
                                        111, 114, 108, 100, 41, 32, 84, 106, 10, 32, 32, 69, 84
                                    ],
                                }),
                            },
                        ],
                    },
                    xrt: PdfXrt {
                        sections: vec![PdfXrtSection {
                            subsections: vec![PdfXrtSubsection {
                                first_obj_num: 0,
                                num_entries: 5,
                                entries: vec![
                                    PdfXrtSubsectionEntry::FreeObject(PdfXrtFreeObject {
                                        obj_num: 0,
                                        gen: 65535,
                                    }),
                                    PdfXrtSubsectionEntry::InUseObject(PdfXrtInUseObject {
                                        offset: 18,
                                        gen: 0,
                                    }),
                                    PdfXrtSubsectionEntry::InUseObject(PdfXrtInUseObject {
                                        offset: 77,
                                        gen: 0,
                                    }),
                                    PdfXrtSubsectionEntry::InUseObject(PdfXrtInUseObject {
                                        offset: 178,
                                        gen: 0
                                    }),
                                    PdfXrtSubsectionEntry::InUseObject(PdfXrtInUseObject {
                                        offset: 457,
                                        gen: 0,
                                    }),
                                ],
                            },],
                        },],
                    },
                    trailer: PdfTrailer {
                        dictionary: pdf_dict!(
                            b"Root"[..].to_vec() => PdfObject::PdfIndirectObjectReference(
                                PdfIndirectObjectReference {
                                    obj_num: 1,
                                    gen_num: 0
                                }
                            ),
                            b"Size"[..].to_vec() => PdfObject::PdfDirectObject(
                                PdfDirectObject::PdfNumber(
                                    PdfNumber::PdfInteger(5)
                                )
                            )
                        ),
                        startxref: 565,
                    },
                },
            ))
        );
    }
}
