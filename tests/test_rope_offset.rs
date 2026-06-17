/// Test the position_to_offset and offset_to_position functions with Chinese characters
use ropey::Rope;
use lsp_types::Position;

// Copy of the functions from src/lib.rs to test in isolation
fn position_to_offset(position: Position, rope: &Rope) -> Option<usize> {
    let line_byte_start = rope.try_line_to_byte(position.line as usize).ok()?;
    let line_text = rope.line(position.line as usize);
    let mut col_byte_offset = 0usize;
    let mut utf16_count = 0u32;
    for ch in line_text.chars() {
        if utf16_count >= position.character {
            break;
        }
        col_byte_offset += ch.len_utf8();
        utf16_count += ch.len_utf16() as u32;
    }
    Some(line_byte_start + col_byte_offset)
}

fn offset_to_position(offset: usize, rope: &Rope) -> Option<Position> {
    let line = rope.try_byte_to_line(offset).ok()?;
    let line_byte_start = rope.try_line_to_byte(line).ok()?;
    let line_text = rope.line(line);
    let mut column = 0u32;
    let mut byte_i = 0usize;
    for ch in line_text.chars() {
        if line_byte_start + byte_i >= offset {
            break;
        }
        column += ch.len_utf16() as u32;
        byte_i += ch.len_utf8();
    }
    Some(Position::new(line as u32, column))
}

#[test]
fn test_position_to_offset_ascii() {
    let rope = Rope::from_str("module foo;");
    // Positions in UTF-16 code units (same as byte offset for ASCII)
    assert_eq!(position_to_offset(Position::new(0, 0), &rope), Some(0));
    assert_eq!(position_to_offset(Position::new(0, 7), &rope), Some(7)); // ' ' at byte 7
    assert_eq!(position_to_offset(Position::new(0, 10), &rope), Some(10)); // ';' at byte 10
    assert_eq!(position_to_offset(Position::new(0, 11), &rope), Some(11)); // past end
}

#[test]
fn test_position_to_offset_chinese() {
    let rope = Rope::from_str("module 变量;");
    // UTF-16 code units: m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7) 量(8) ;(9)
    // Byte offsets:       m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7,8,9) 量(10,11,12) ;(13)

    // Position (0, 7) = '变' (1 UTF-16 code unit)
    assert_eq!(position_to_offset(Position::new(0, 7), &rope), Some(7));
    // Position (0, 8) = '量' (1 UTF-16 code unit, at byte 10)
    assert_eq!(position_to_offset(Position::new(0, 8), &rope), Some(10));
    // Position (0, 9) = ';' (1 UTF-16 code unit, at byte 13)
    assert_eq!(position_to_offset(Position::new(0, 9), &rope), Some(13));
    // Position (0, 0) = start
    assert_eq!(position_to_offset(Position::new(0, 0), &rope), Some(0));
}

#[test]
fn test_offset_to_position_chinese() {
    let rope = Rope::from_str("module 变量;");
    // Byte offsets: 0=m ... 6=' '  7=变 8=变 9=变  10=量 11=量 12=量  13=;

    // Byte offset 7 = start of '变' → Position (0, 7)
    assert_eq!(offset_to_position(7, &rope), Some(Position::new(0, 7)));
    // Byte offset 10 = start of '量' → Position (0, 8)
    assert_eq!(offset_to_position(10, &rope), Some(Position::new(0, 8)));
    // Byte offset 13 = ';' → Position (0, 9)
    assert_eq!(offset_to_position(13, &rope), Some(Position::new(0, 9)));
}

#[test]
fn test_incremental_edit_ascii() {
    // Simulate: buffer = "module foo;"
    // Editor sends: range start=char 7, end=char 10, text="bar"
    // This replaces "foo" (chars 7,8,9) with "bar", giving "module bar;"
    let mut rope = Rope::from_str("module foo;");
    let start_byte = position_to_offset(Position::new(0, 7), &rope).unwrap();
    let end_byte = position_to_offset(Position::new(0, 10), &rope).unwrap();
    // Convert byte offsets to char offsets (the fix for non-ASCII)
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "bar");
    assert_eq!(rope.to_string(), "module bar;");
}

#[test]
fn test_incremental_edit_chinese() {
    // Simulate: buffer = "module 变量;"
    // Editor sends: range start=char 9, end=char 9, text="测试"  (insert after 变量)
    // Expected: "module 变量测试;"
    let mut rope = Rope::from_str("module 变量;");
    let start_byte = position_to_offset(Position::new(0, 9), &rope).unwrap(); // byte 13 = ';'
    let end_byte = position_to_offset(Position::new(0, 9), &rope).unwrap();
    // Convert byte offsets to char offsets (the FIX)
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "测试");
    assert_eq!(rope.to_string(), "module 变量测试;");

    // Now replace "变量测试" with "你好"
    // After insert, string is "module 变量测试;" which is:
    // m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7) 量(8) 测(9) 试(10) ;(11)  [char indices]
    // m(0) o(1) d(2) u(3) l(4) e(5) ' '(6) 变(7,8,9) 量(10,11,12) 测(13,14,15) 试(16,17,18) ;(19)  [byte indices]
    let start_byte = position_to_offset(Position::new(0, 7), &rope).unwrap(); // '变'
    let end_byte = position_to_offset(Position::new(0, 11), &rope).unwrap(); // after '试'
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "你好");
    assert_eq!(rope.to_string(), "module 你好;");
}

#[test]
fn test_roundtrip_conversion() {
    let texts = vec![
        "module simple;",
        "module 变量;",
        "module 变量测试;",
        " 空格 测试 123",
        "let x = 你好世界;",
        "type 布尔 = True | False; // 中文注释",
    ];

    for text in texts {
        let rope = Rope::from_str(text);
        for line in 0..rope.len_lines() {
            let line_text = rope.line(line);
            let mut utf16_pos = 0u32;
            // Test each character boundary
            for ch in line_text.chars() {
                let offset = position_to_offset(Position::new(line as u32, utf16_pos), &rope).unwrap();
                // Verify the offset points to the start of this character
                let line_start = rope.try_line_to_byte(line).unwrap();
                assert_eq!(offset, line_start + line_text.chars().take(utf16_pos as usize).map(|c| c.len_utf8()).sum::<usize>(),
                    "Failed for text {:?}, line {}, char {}", text, line, utf16_pos);

                // Round-trip: position → offset → position
                let pos_back = offset_to_position(offset, &rope).unwrap();
                assert_eq!(pos_back, Position::new(line as u32, utf16_pos),
                    "Round-trip failed for text {:?}, line {}, char {}", text, line, utf16_pos);

                utf16_pos += ch.len_utf16() as u32;
            }

            // Test end-of-line position
            let eol_offset = position_to_offset(Position::new(line as u32, utf16_pos), &rope).unwrap();
            let eol_pos = offset_to_position(eol_offset, &rope).unwrap();
            assert_eq!(eol_pos, Position::new(line as u32, utf16_pos),
                "EOL round-trip failed for text {:?}, line {}", text, line);
        }
    }
}

#[test]
fn test_rope_remove_insert_chinese() {
    // Simulate the did_change flow with byte→char conversion
    let mut rope = Rope::from_str("module a;// 你好世界");

    // Delete "a" and insert "变量"
    // "a" is at UTF-16 position 7, byte 7
    // After "a" is at UTF-16 position 8, byte 8
    let start_byte = position_to_offset(Position::new(0, 7), &rope).unwrap();
    let end_byte = position_to_offset(Position::new(0, 8), &rope).unwrap();
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "变量");

    // Expected: "module 变量;// 你好世界"
    assert_eq!(rope.to_string(), "module 变量;// 你好世界");
}

#[test]
fn test_did_change_simulation() {
    // Simulate the exact did_change flow:
    // buffer = "module 变量;"
    // Editor sends: range start=char 9, end=char 9, text="测试"
    let buffer = "module 变量;".to_string();
    let rope = Rope::from_str(&buffer);
    let start_byte = position_to_offset(Position::new(0, 9), &rope).unwrap();
    let end_byte = position_to_offset(Position::new(0, 9), &rope).unwrap();
    let mut rope = rope;
    let start_char = rope.byte_to_char(start_byte);
    let end_char = rope.byte_to_char(end_byte);
    rope.remove(start_char..end_char);
    rope.insert(start_char, "测试");
    let result = rope.to_string();
    assert_eq!(result, "module 变量测试;");
}
