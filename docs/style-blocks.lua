-- Quarto Lua filter to visually differentiate Lean 4, Python, and Result output blocks.

local function has_class(el, target)
  for _, c in ipairs(el.classes) do
    if c == target then
      return true
    end
  end
  return false
end

function CodeBlock(el)
  if FORMAT:match("latex") then
    if has_class(el, "lean") then
      return {
        pandoc.RawBlock("latex", "\\begin{leanbox}"),
        el,
        pandoc.RawBlock("latex", "\\end{leanbox}"),
      }
    elseif has_class(el, "python") then
      return {
        pandoc.RawBlock("latex", "\\begin{pythonbox}"),
        el,
        pandoc.RawBlock("latex", "\\end{pythonbox}"),
      }
    end
  end
  return el
end

function Div(el)
  if FORMAT:match("latex") then
    if has_class(el, "cell-output-stdout") or has_class(el, "cell-output") then
      -- Only wrap text output blocks, not figures
      local has_code = false
      for _, blk in ipairs(el.content) do
        if blk.t == "CodeBlock" then
          has_code = true
          break
        end
      end
      if has_code then
        return {
          pandoc.RawBlock("latex", "\\begin{resultbox}"),
          el,
          pandoc.RawBlock("latex", "\\end{resultbox}"),
        }
      end
    end
  end
  return el
end
