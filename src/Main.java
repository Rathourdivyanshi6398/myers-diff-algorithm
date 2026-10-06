import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

public class Main {
    // The three kinds of step in an edit script.
    static final byte KEEP = 0, DELETE = 1, INSERT = 2;

    // ---------- reading ----------

    // Raw bytes -> String using ISO_8859_1 (1 byte = 1 char, nothing is lost),
    // then split on '\n'. A '\r' stays inside the line.
    static List<String> splitIntoLines(byte[] fileBytes) {
        String text = new String(fileBytes, StandardCharsets.ISO_8859_1);
        List<String> lines = new ArrayList<>();
        int lineStart = 0;
        for (int position = 0; position < text.length(); position++) {
            if (text.charAt(position) == '\n') {
                lines.add(text.substring(lineStart, position));
                lineStart = position + 1;
            }
        }
        if (lineStart < text.length()) {                 // last piece only if it is not empty
            lines.add(text.substring(lineStart));
        }
        return lines;
    }

    // Give every distinct line a number, so Myers compares ints instead of long strings.
    // The same map is used for both files, so equal lines get equal numbers.
    static int[] mapLinesToIds(List<String> lines, Map<String, Integer> lineIdMap) {
        int[] lineIds = new int[lines.size()];
        for (int lineNumber = 0; lineNumber < lineIds.length; lineNumber++) {
            String line = lines.get(lineNumber);
            Integer id = lineIdMap.get(line);
            if (id == null) {
                id = lineIdMap.size();                   // next unused number
                lineIdMap.put(line, id);
            }
            lineIds[lineNumber] = id;
        }
        return lineIds;
    }

    // ---------- Myers ----------

    // Trims the common start and end, handles the "one side is empty" case,
    // then runs the real Myers search only on the part in the middle.
    // Returns the full edit script: one KEEP / DELETE / INSERT per step.
    static byte[] myersDiff(int[] oldItems, int[] newItems) {
        int oldLength = oldItems.length;
        int newLength = newItems.length;

        int commonPrefix = 0;                            // items equal at the start
        while (commonPrefix < oldLength && commonPrefix < newLength
                && oldItems[commonPrefix] == newItems[commonPrefix]) {
            commonPrefix++;
        }
        int commonSuffix = 0;                            // items equal at the end
        while (commonSuffix < oldLength - commonPrefix && commonSuffix < newLength - commonPrefix
                && oldItems[oldLength - 1 - commonSuffix] == newItems[newLength - 1 - commonSuffix]) {
            commonSuffix++;
        }

        int[] oldMiddle = Arrays.copyOfRange(oldItems, commonPrefix, oldLength - commonSuffix);
        int[] newMiddle = Arrays.copyOfRange(newItems, commonPrefix, newLength - commonSuffix);

        byte[] middleSteps;
        if (oldMiddle.length == 0) {                     // only insertions are left
            middleSteps = new byte[newMiddle.length];
            Arrays.fill(middleSteps, INSERT);
        } else if (newMiddle.length == 0) {              // only deletions are left
            middleSteps = new byte[oldMiddle.length];
            Arrays.fill(middleSteps, DELETE);
        } else {
            middleSteps = myersCore(oldMiddle, newMiddle);
        }

        // prefix keeps + middle steps + suffix keeps (KEEP is 0, so new bytes are already KEEP)
        byte[] allSteps = new byte[commonPrefix + middleSteps.length + commonSuffix];
        System.arraycopy(middleSteps, 0, allSteps, commonPrefix, middleSteps.length);
        return allSteps;
    }

    // The real Myers O(ND) algorithm.
    // Picture a grid: moving right = delete, moving down = insert,
    // moving diagonally = keep (free, only when the items are equal).
    static byte[] myersCore(int[] oldItems, int[] newItems) {
        int oldLength = oldItems.length;
        int newLength = newItems.length;
        int maxEdits = oldLength + newLength;            // worst case: delete all + insert all
        int offset = maxEdits + 1;                       // shifts diagonal numbers so they can be array indexes

        // furthestX[offset + diagonal] = furthest x reached on that diagonal (diagonal = x - y)
        int[] furthestX = new int[2 * maxEdits + 3];

        // Remembers furthestX of every round, so we can walk backwards later.
        // Round "edits" is stored from index edits*(edits+1)/2 onward, using edits+1 numbers
        // (one for each diagonal -edits, -edits+2, ..., +edits).
        int[] traceStorage = new int[1 << 16];

        int minimumEdits = 0;
        search:
        for (int edits = 0; edits <= maxEdits; edits++) {
            int roundStart = edits * (edits + 1) / 2;
            if (roundStart + edits + 1 > traceStorage.length) {          // grow by doubling (rarely)
                traceStorage = Arrays.copyOf(traceStorage,
                        Math.max(traceStorage.length * 2, roundStart + edits + 1));
            }
            for (int diagonal = -edits; diagonal <= edits; diagonal += 2) {
                int oldPos;
                boolean cameFromAbove = diagonal == -edits
                        || (diagonal != edits
                            && furthestX[offset + diagonal - 1] < furthestX[offset + diagonal + 1]);
                if (cameFromAbove) {
                    oldPos = furthestX[offset + diagonal + 1];           // move down  = insert
                } else {
                    oldPos = furthestX[offset + diagonal - 1] + 1;       // move right = delete
                }
                int newPos = oldPos - diagonal;

                // snake: follow equal items diagonally for free
                while (oldPos < oldLength && newPos < newLength
                        && oldItems[oldPos] == newItems[newPos]) {
                    oldPos++;
                    newPos++;
                }

                furthestX[offset + diagonal] = oldPos;
                traceStorage[roundStart + (diagonal + edits) / 2] = oldPos;   // save for backtracking

                if (oldPos >= oldLength && newPos >= newLength) {        // reached the bottom-right corner
                    minimumEdits = edits;
                    break search;
                }
            }
        }

        // Walk back from the end (oldLength, newLength) to the start (0, 0).
        // Steps are collected in reverse order and flipped at the end.
        byte[] reversedSteps = new byte[maxEdits];
        int stepCount = 0;
        int oldPos = oldLength;
        int newPos = newLength;
        for (int edits = minimumEdits; edits > 0; edits--) {
            int previousRoundStart = (edits - 1) * edits / 2;            // where round edits-1 is stored
            int diagonal = oldPos - newPos;
            int slot = (diagonal + edits) / 2;
            // In round edits-1: diagonal-1 is at previousRoundStart + slot - 1,
            //                   diagonal+1 is at previousRoundStart + slot.
            boolean cameFromAbove;
            if (diagonal == -edits) {
                cameFromAbove = true;
            } else if (diagonal == edits) {
                cameFromAbove = false;
            } else {
                cameFromAbove = traceStorage[previousRoundStart + slot - 1]
                              < traceStorage[previousRoundStart + slot];
            }
            int previousDiagonal = cameFromAbove ? diagonal + 1 : diagonal - 1;
            int previousOldPos = cameFromAbove
                    ? traceStorage[previousRoundStart + slot]
                    : traceStorage[previousRoundStart + slot - 1];
            int previousNewPos = previousOldPos - previousDiagonal;

            // the point right after the single edit (where the snake started)
            int afterEditOldPos = cameFromAbove ? previousOldPos : previousOldPos + 1;
            int afterEditNewPos = afterEditOldPos - diagonal;

            while (oldPos > afterEditOldPos && newPos > afterEditNewPos) {   // the snake = KEEPs
                reversedSteps[stepCount++] = KEEP;
                oldPos--;
                newPos--;
            }
            reversedSteps[stepCount++] = cameFromAbove ? INSERT : DELETE;    // the edit itself
            oldPos = previousOldPos;
            newPos = previousNewPos;
        }
        while (oldPos > 0 && newPos > 0) {                                   // first snake (0 edits)
            reversedSteps[stepCount++] = KEEP;
            oldPos--;
            newPos--;
        }

        byte[] steps = new byte[stepCount];
        for (int i = 0; i < stepCount; i++) {
            steps[i] = reversedSteps[stepCount - 1 - i];
        }
        return steps;
    }

    // ---------- Part B: highlighting ----------

    // Turns a list of changed/not-changed flags into text like "3-5,9-12".
    // The end number is not included. Returns "." when nothing changed.
    static String buildRanges(boolean[] isChanged) {
        StringBuilder ranges = new StringBuilder();
        int position = 0;
        while (position < isChanged.length) {
            if (!isChanged[position]) {
                position++;
                continue;
            }
            int rangeEnd = position;
            while (rangeEnd < isChanged.length && isChanged[rangeEnd]) {
                rangeEnd++;
            }
            if (ranges.length() > 0) {
                ranges.append(',');
            }
            ranges.append(position).append('-').append(rangeEnd);
            position = rangeEnd;
        }
        return ranges.length() == 0 ? "." : ranges.toString();
    }

    // The line is stored as Latin-1 text. Convert back to the original bytes,
    // decode those as UTF-8, and return one number per Unicode character (code point).
    static int[] toCodePoints(String latin1Line) {
        byte[] originalBytes = latin1Line.getBytes(StandardCharsets.ISO_8859_1);
        return new String(originalBytes, StandardCharsets.UTF_8).codePoints().toArray();
    }

    // Runs Myers again, this time on the characters of one deleted line and one inserted line.
    static String highlight(String oldLine, String newLine) {
        int[] oldChars = toCodePoints(oldLine);
        int[] newChars = toCodePoints(newLine);
        boolean[] oldCharChanged = new boolean[oldChars.length];
        boolean[] newCharChanged = new boolean[newChars.length];

        int oldIndex = 0;
        int newIndex = 0;
        for (byte step : myersDiff(oldChars, newChars)) {
            if (step == KEEP) {
                oldIndex++;
                newIndex++;
            } else if (step == DELETE) {
                oldCharChanged[oldIndex] = true;
                oldIndex++;
            } else {
                newCharChanged[newIndex] = true;
                newIndex++;
            }
        }
        return "? " + buildRanges(oldCharChanged) + " | " + buildRanges(newCharChanged);
    }

    // ---------- output ----------

    // Writes prefix + line + '\n' as raw bytes (same Latin-1 mapping as reading, so nothing changes).
    static void writeLine(OutputStream out, String prefix, String line) throws IOException {
        out.write(prefix.getBytes(StandardCharsets.ISO_8859_1));
        out.write(line.getBytes(StandardCharsets.ISO_8859_1));
        out.write('\n');
    }

    public static void main(String[] args) throws IOException {
        boolean known = args.length == 3 && (args[0].equals("lines") || args[0].equals("highlight"));
        if (!known) {
            System.err.println("usage: Main lines|highlight A_PATH B_PATH");
            System.exit(2);
        }
        String command = args[0];
        String aPath = args[1];
        String bPath = args[2];

        // read both files as raw bytes (unreadable file -> nothing on stdout, exit code 2)
        byte[] oldFileBytes = null;
        byte[] newFileBytes = null;
        try {
            oldFileBytes = Files.readAllBytes(Path.of(aPath));
            newFileBytes = Files.readAllBytes(Path.of(bPath));
        } catch (IOException | RuntimeException e) {
            System.err.println("cannot read input: " + e.getMessage());
            System.exit(2);
        }

        boolean withHighlights = command.equals("highlight");
        List<String> oldLines = splitIntoLines(oldFileBytes);
        List<String> newLines = splitIntoLines(newFileBytes);

        Map<String, Integer> lineIdMap = new HashMap<>();
        int[] oldLineIds = mapLinesToIds(oldLines, lineIdMap);
        int[] newLineIds = mapLinesToIds(newLines, lineIdMap);
        byte[] steps = myersDiff(oldLineIds, newLineIds);

        OutputStream out = new BufferedOutputStream(new FileOutputStream(FileDescriptor.out), 1 << 16);

        int stepIndex = 0;          // position in the edit script
        int oldLineIndex = 0;       // next unread line of the old file
        int newLineIndex = 0;       // next unread line of the new file
        while (stepIndex < steps.length) {
            if (steps[stepIndex] == KEEP) {
                writeLine(out, " ", oldLines.get(oldLineIndex));
                oldLineIndex++;
                newLineIndex++;
                stepIndex++;
                continue;
            }

            // A change block = a run of DELETE/INSERT steps with no KEEP in between.
            int blockEnd = stepIndex;
            int deleteCount = 0;
            int insertCount = 0;
            while (blockEnd < steps.length && steps[blockEnd] != KEEP) {
                if (steps[blockEnd] == DELETE) {
                    deleteCount++;
                } else {
                    insertCount++;
                }
                blockEnd++;
            }

            // Rule: inside a block, print all '-' lines before any '+' line.
            for (int n = 0; n < deleteCount; n++) {
                writeLine(out, "-", oldLines.get(oldLineIndex + n));
            }
            for (int n = 0; n < insertCount; n++) {
                writeLine(out, "+", newLines.get(newLineIndex + n));
                boolean hasPartner = n < deleteCount;    // 1st '+' pairs with 1st '-', and so on
                if (withHighlights && hasPartner) {
                    writeLine(out, "", highlight(oldLines.get(oldLineIndex + n),
                                                 newLines.get(newLineIndex + n)));
                }
            }
            oldLineIndex += deleteCount;
            newLineIndex += insertCount;
            stepIndex = blockEnd;
        }
        out.flush();
    }
}