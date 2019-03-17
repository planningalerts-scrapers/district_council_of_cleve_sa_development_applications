// Parses the development applications at the South Australian District Council of Cleve web site
// and places them in a database.
//
// Michael Bone
// 17th March 2019
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const fs = require("fs");
const cheerio = require("cheerio");
const request = require("request-promise-native");
const sqlite3 = require("sqlite3");
const urlparser = require("url");
const moment = require("moment");
const pdfjs = require("pdfjs-dist");
const didyoumean2_1 = require("didyoumean2"), didyoumean = didyoumean2_1;
sqlite3.verbose();
const DevelopmentApplicationsUrl = "https://www.cleve.sa.gov.au/registers";
const CommentUrl = "mailto:council@cleve.sa.gov.au";
// All valid street names, street suffixes, suburb names and hundred names.
let StreetNames = null;
let StreetSuffixes = null;
let SuburbNames = null;
let HundredNames = null;
// Sets up an sqlite database.
async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text, [legal_description] text)");
            resolve(database);
        });
    });
}
// Inserts a row in the database if the row does not already exist.
async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or ignore into [data] values (?, ?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate,
            developmentApplication.legalDescription
        ], function (error, row) {
            if (error) {
                console.error(error);
                reject(error);
            }
            else {
                if (this.changes > 0)
                    console.log(`    Inserted: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\", legal description \"${developmentApplication.legalDescription}\" and received date \"${developmentApplication.receivedDate}\" into the database.`);
                else
                    console.log(`    Skipped: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\", legal description \"${developmentApplication.legalDescription}\" and received date \"${developmentApplication.receivedDate}\" because it was already present in the database.`);
                sqlStatement.finalize(); // releases any locks
                resolve(row);
            }
        });
    });
}
// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.  Take care to avoid extremely tall elements (because these may otherwise
// be considered as part of all rows and effectively force the return value of this function to
// the same value, regardless of the value of startElement).
function getRowTop(elements, startElement) {
    let top = startElement.y;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y) // check for overlap
            if (getVerticalOverlapPercentage(startElement, element) > 50) // avoids extremely tall elements
                if (element.y < top)
                    top = element.y;
    return top;
}
// Constructs a rectangle based on the intersection of the two specified rectangles.
function intersect(rectangle1, rectangle2) {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}
// Calculates the square of the Euclidean distance between two elements.
function calculateDistance(element1, element2) {
    let point1 = { x: element1.x + element1.width, y: element1.y + element1.height / 2 };
    let point2 = { x: element2.x, y: element2.y + element2.height / 2 };
    if (point2.x < point1.x - element1.width / 5) // arbitrary overlap factor of 20% (ie. ignore elements that overlap too much in the horizontal direction)
        return Number.MAX_VALUE;
    return (point2.x - point1.x) * (point2.x - point1.x) + (point2.y - point1.y) * (point2.y - point1.y);
}
// Determines whether there is vertical overlap between two elements.
function isVerticalOverlap(element1, element2) {
    return element2.y < element1.y + element1.height && element2.y + element2.height > element1.y;
}
// Gets the percentage of vertical overlap between two elements (0 means no overlap and 100 means
// 100% overlap; and, for example, 20 means that 20% of the second element overlaps somewhere
// with the first element).
function getVerticalOverlapPercentage(element1, element2) {
    let y1 = Math.max(element1.y, element2.y);
    let y2 = Math.min(element1.y + element1.height, element2.y + element2.height);
    return (y2 < y1) ? 0 : (((y2 - y1) * 100) / element2.height);
}
// Gets the element immediately to the right of the specified element (but ignores elements that
// appear after a large horizontal gap).
function getRightElement(elements, element) {
    let closestElement = { text: undefined, x: Number.MAX_VALUE, y: Number.MAX_VALUE, width: 0, height: 0 };
    for (let rightElement of elements)
        if (isVerticalOverlap(element, rightElement) && // ensure that there is at least some vertical overlap
            getVerticalOverlapPercentage(element, rightElement) > 50 && // avoid extremely tall elements (ensure at least 50% overlap)
            (rightElement.x > element.x + element.width) && // ensure the element actually is to the right
            (rightElement.x - (element.x + element.width) < 30) && // avoid elements that appear after a large gap (arbitrarily ensure less than a 30 pixel gap horizontally)
            calculateDistance(element, rightElement) < calculateDistance(element, closestElement)) // check if closer than any element encountered so far
            closestElement = rightElement;
    return (closestElement.text === undefined) ? undefined : closestElement;
}
// Finds the element that most closely matches the specified text.
function findElement(elements, text, shouldSelectRightmostElement) {
    // Examine all the elements on the page that being with the same character as the requested
    // text.
    let condensedText = text.replace(/[\s,\-_]/g, "").toLowerCase();
    let firstCharacter = condensedText.charAt(0);
    let matches = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith(firstCharacter))) {
        // Extract up to 5 elements to the right of the element that has text starting with the
        // required character (and so may be the start of the requested text).  Join together the
        // elements to the right in an attempt to find the best match to the text.
        let rightElement = element;
        let rightElements = [];
        do {
            rightElements.push(rightElement);
            let currentText = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();
            if (currentText.length > condensedText.length + 2) // stop once the text is too long
                break;
            if (currentText.length >= condensedText.length - 2) { // ignore until the text is close to long enough
                if (currentText === condensedText)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 0, text: currentText });
                else if (didyoumean2_1.default(currentText, [condensedText], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 1, text: currentText });
                else if (didyoumean2_1.default(currentText, [condensedText], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 2, text: currentText });
            }
            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5); // up to 5 elements
    }
    // Chose the best match (if any matches were found).  Note that trimming is performed here so
    // that text such as "  Plan" is matched in preference to text such as "plan)" (when looking
    // for elements that match "Plan").  For an example of this problem see "200/303/07" in
    // "https://www.walkerville.sa.gov.au/webdata/resources/files/DA%20Register%20-%202007.pdf".
    //
    // Note that if the match is made of several elements then sometimes the caller requires the
    // left most element and sometimes the right most element (depending on where further text
    // will be searched for relative to this "found" element).
    if (matches.length > 0) {
        let bestMatch = matches.reduce((previous, current) => (previous === undefined ||
            current.threshold < previous.threshold ||
            (current.threshold === previous.threshold && Math.abs(current.text.trim().length - condensedText.length) < Math.abs(previous.text.trim().length - condensedText.length)) ? current : previous), undefined);
        return shouldSelectRightmostElement ? bestMatch.rightElement : bestMatch.leftElement;
    }
    return undefined;
}
// Finds the start element of each development application on the current PDF page (there are
// typically two development applications on a single page and each development application
// typically begins with the text "Application Number").
function findStartElements(elements) {
    // Examine all the elements on the page that being with "A" or "a".
    let startElements = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith("a"))) {
        // Extract up to 5 elements to the right of the element that has text starting with
        // the letter "a" (and so may be the start of the "Application Number" text).  Join
        // together the elements to the right in an attempt to find the best match to the text
        // "Application Number".
        let rightElement = element;
        let rightElements = [];
        let matches = [];
        do {
            rightElements.push(rightElement);
            // Allow for common misspellings of the "no." text.
            let text = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();
            if (text.length >= 20) // stop once the text is too long
                break;
            if (text.length >= 17) { // ignore until the text is close to long enough
                if (text === "applicationnumber")
                    matches.push({ element: rightElement, threshold: 0, text: text });
                else if (didyoumean2_1.default(text, ["ApplicationNumber"], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 1, text: text });
                else if (didyoumean2_1.default(text, ["ApplicationNumber"], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 2, text: text });
            }
            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5); // up to 5 elements
        // Chose the best match (if any matches were found).
        if (matches.length > 0) {
            let bestMatch = matches.reduce((previous, current) => (previous === undefined ||
                current.threshold < previous.threshold ||
                (current.threshold === previous.threshold && Math.abs(current.text.trim().length - "ApplicationNumber".length) < Math.abs(previous.text.trim().length - "ApplicationNumber".length)) ? current : previous), undefined);
            startElements.push(bestMatch.element);
        }
    }
    // Ensure the start elements are sorted in the order that they appear on the page.
    let yComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
    startElements.sort(yComparer);
    return startElements;
}
// Gets the text to the right in a rectangle, where the rectangle is delineated by the positions
// in which the three specified strings of (case sensitive) text are found.
function getRightText(elements, topLeftText, rightText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topLeftElement = findElement(elements, topLeftText, true);
    let rightElement = (rightText === undefined) ? undefined : findElement(elements, rightText, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false);
    if (topLeftElement === undefined)
        return undefined;
    let x = topLeftElement.x + topLeftElement.width;
    let y = topLeftElement.y;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;
    // Sort the elements by Y co-ordinate and then by X co-ordinate.
    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);
    // Join the elements into a single string.
    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}
// Gets the text to the left in a rectangle, where the rectangle is delineated by the positions
// in which the three specified strings of (case sensitive) text are found.
function getLeftText(elements, topRightText, leftText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topRightElement = findElement(elements, topRightText, true);
    let leftElement = (leftText === undefined) ? undefined : findElement(elements, leftText, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false);
    if (topRightElement === undefined || leftElement === undefined || bottomElement === undefined)
        return undefined;
    let x = leftElement.x + leftElement.width;
    let y = topRightElement.y;
    let width = topRightElement.x - x;
    let height = bottomElement.y - y;
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;
    // Sort the elements by Y co-ordinate and then by X co-ordinate.
    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);
    // Join the elements into a single string.
    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}
// Gets the text downwards in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.
function getDownText(elements, topText, rightText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topElement = findElement(elements, topText, true);
    let rightElement = (rightText === undefined) ? undefined : findElement(elements, rightText, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false);
    if (topElement === undefined)
        return undefined;
    let x = topElement.x;
    let y = topElement.y + topElement.height;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;
    // Sort the elements by Y co-ordinate and then by X co-ordinate.
    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);
    // Join the elements into a single string.
    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}
// Constructs the full address string based on the specified address components.
function formatAddress(houseNumber, streetName, suburbName) {
    suburbName = suburbName.replace(/^HD WARD\//i, "").replace(/HD OF /i, "").replace(/^HD /i, "").replace(/ HD$/i, "").replace(/ SA$/, "").trim();
    suburbName = SuburbNames[suburbName.toUpperCase()] || suburbName;
    let separator = ((houseNumber !== "" || streetName !== "") && suburbName !== "") ? ", " : "";
    return `${houseNumber} ${streetName}${separator}${suburbName}`.trim().replace(/\s\s+/g, " ").toUpperCase().replace(/\*/g, "");
}
// Parses the address from the house number, street name and suburb name.  Note that these
// address components may actually contain multiple addresses (delimited by "ü" characters).
function parseAddress(houseNumber, streetName, suburbName) {
    // Two or more addresses are sometimes recorded in the same field.  This is done in a way
    // which is ambiguous (ie. it is not possible to reconstruct the original addresses perfectly).
    //
    // For example, the following address:
    //
    //     House Number: ü35
    //           Street: RAILWAYüSCHOOL TCE SOUTHüTERRA
    //           Suburb: PASKEVILLEüPASKEVILLE
    //
    // should be interpreted as the following two addresses:
    //
    //     RAILWAY TCE SOUTH, PASKEVILLE
    //     35 SCHOOL TERRA(CE), PASKEVILLE
    //
    // whereas the following address:
    //
    //     House Number: 79ü4
    //           Street: ROSSLYNüSWIFT WINGS ROADüROAD
    //           Suburb: WALLAROOüWALLAROO
    //
    // should be interpreted as the following two addresses:
    //
    //     79 ROSSLYN ROAD, WALLAROO
    //     4 SWIFT WINGS ROAD, WALLAROO
    //
    // And so notice that in the first case above the "TCE" text of the Street belonged to the
    // first address.  Whereas in the second case above the "WINGS" text of the Street belonged
    // to the second address (this was deduced by examining actual existing street names).
    if (!houseNumber.includes("ü"))
        return formatAddress(houseNumber, streetName, suburbName);
    // Split the house number on the "ü" character.
    let houseNumberTokens = houseNumber.split("ü");
    // Split the suburb name on the "ü" character.
    let suburbNameTokens = suburbName.split("ü");
    // The street name will have twice as many "ü" characters as the house number.  Each street
    // name is broken in two and the resulting strings are joined into two groups (delimited
    // by "ü" within the groups).  A single space is used to join the two groups together.
    //
    // For example, the street names "WALLACE STREET" and "MAY TERRACE" are broken in two as
    // "WALLACE" and "STREET"; and "MAY" and "TERRACE".  And then joined back together into
    // two groups, "WALLACEüMAY" and "STREETüTERRACE".  Those two groups are then concatenated
    // together using a single intervening space to form "WALLACEüMAY STREETüTERRACE".
    //
    // Unfortunately, the street name is truncated at 30 characters so some of the "ü" characters
    // may be missing.  Also note that there is an ambiguity in some cases as to whether a space
    // is a delimiter or is just a space that happens to occur within a street name or suffix 
    // (such as "Kybunga Top" in "Kybunga Top Road" or "TERRACE SOUTH" in "RAILWAY TERRACE SOUTH").
    //
    // For example,
    //
    //     PHILLIPSüHARBISON ROADüROAD     <-- street names broken in two and joined into groups
    //     BarrüFrances StreetüTerrace     <-- street names broken in two and joined into groups
    //     GOYDERüGOYDERüMail HDüHDüRoad   <-- street names broken in two and joined into groups
    //     ORIENTALüWINDJAMMER COURTüCOUR  <-- truncated street suffix
    //     TAYLORüTAYLORüTAYLOR STREETüST  <-- missing "ü" character due to truncation
    //     EDGARüEASTüEAST STREETüTERRACE  <-- missing "ü" character due to truncation
    //     SOUTH WESTüSOUTH WEST TERRACEü  <-- missing "ü" character due to truncation
    //     ChristopherüChristopher Street  <-- missing "ü" character due to truncation
    //     PORT WAKEFIELDüPORT WAKEFIELD   <-- missing "ü" character due to truncation
    //     KENNETT STREETüKENNETT STREET   <-- missing "ü" character due to truncation (the missing text is probably " SOUTHüSOUTH")
    //     NORTH WESTüNORTH WESTüNORTH WE  <-- missing "ü" characters due to truncation
    //     RAILWAYüSCHOOL TCE SOUTHüTERRA  <-- ambiguous space delimiter
    //     BLYTHüWHITE WELL HDüROAD        <-- ambiguous space delimiter
    //     Kybunga TopüKybunga Top RoadüR  <-- ambiguous space delimiter
    //     SOUTHüSOUTH TERRACE EASTüTERRA  <-- ambiguous space delimiter
    // Artificially increase the street name tokens to twice the length (minus one) of the house
    // number tokens (this then simplifies the following processing).  The "minus one" is because
    // the middle token will be split in two later.
    let streetNameTokens = streetName.split("ü");
    while (streetNameTokens.length < 2 * houseNumberTokens.length - 1)
        streetNameTokens.push("");
    // Consider the following street name (however, realistically this would be truncated at
    // 30 characters; this is ignored for the sake of explaining the parsing),
    //
    //     Kybunga TopüSmithüRailway South RoadüTerrace EastüTerrace
    //
    // This street name would be split into the following tokens,
    //
    //     Token 0: Kybunga Top
    //     Token 1: Smith
    //     Token 2: Railway South Road  <-- the middle token contains a delimiting space (it is ambiguous as to which space is the correct delimiter)
    //     Token 3: Terrace East
    //     Token 4: Terrace
    //
    // And from these tokens, the following candidate sets of tokens would be constructed (each
    // broken into two groups).  Note that the middle token [Railway South Road] is broken into
    // two tokens in different ways depending on which space is chosen as the delimiter for the
    // groups: [Railway] and [South Road] or [Railway South] and [Road].
    //
    //     Candidate 1: [Kybunga Top] [Smith] [Railway]   [South Road] [Terrace East] [Terrace]
    //                 └───────────╴Group 1╶───────────┘ └──────────────╴Group 2╶──────────────┘
    //
    //     Candidate 2: [Kybunga Top] [Smith] [Railway South]   [Road] [Terrace East] [Terrace]
    //                 └──────────────╴Group 1╶──────────────┘ └───────────╴Group 2╶───────────┘
    let candidates = [];
    let middleTokenIndex = houseNumberTokens.length - 1;
    if (!streetNameTokens[middleTokenIndex].includes(" ")) // the space may be missing if the street name is truncated at 30 characters
        streetNameTokens[middleTokenIndex] += " "; // artificially add a space to simplify the processing
    let ambiguousTokens = streetNameTokens[middleTokenIndex].split(" ");
    for (let index = 1; index < ambiguousTokens.length; index++) {
        let group1 = [...streetNameTokens.slice(0, middleTokenIndex), ambiguousTokens.slice(0, index).join(" ")];
        let group2 = [ambiguousTokens.slice(index).join(" "), ...streetNameTokens.slice(middleTokenIndex + 1)];
        candidates.push({ group1: group1, group2: group2, hasInvalidHundredName: false });
    }
    // Full street names (with suffixes) can now be constructed for each candidate (by joining
    // together corresponding tokens from each group of tokens).
    let addresses = [];
    for (let candidate of candidates) {
        for (let index = 0; index < houseNumberTokens.length; index++) {
            // Expand street suffixes such as "Tce" to "TERRACE".
            let streetSuffix = candidate.group2[index].split(" ")
                .map(token => (StreetSuffixes[token.toUpperCase()] === undefined) ? token : StreetSuffixes[token.toUpperCase()])
                .join(" ");
            // Construct the full street name (including the street suffix).
            let houseNumber = houseNumberTokens[index];
            let streetName = (candidate.group1[index] + " " + streetSuffix).trim().replace(/\s\s+/g, " ");
            if (streetName === "")
                continue; // ignore blank street names
            // Check whether the street name is actually a hundred name such as "BARUNGA HD".
            if (streetName.startsWith("HD ") || streetName.endsWith(" HD") || streetName.toUpperCase().endsWith(" HUNDRED")) { // very likely a hundred name
                let hundredNameMatch = didyoumean2_1.default(streetName.slice(0, -3), HundredNames, { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 0, trimSpaces: true });
                if (hundredNameMatch === null)
                    candidate.hasInvalidHundredName = true; // remember that there is an invalid hundred name (for example, "BARUNGA View HD")
                continue; // ignore all hundred names names
            }
            // Determine the associated suburb name.
            let associatedSuburbName = suburbNameTokens[index];
            if (associatedSuburbName === undefined || associatedSuburbName.trim() === "")
                continue; // ignore blank suburb names
            // Choose the best matching street name (from the known street names).
            let streetNameMatch = didyoumean2_1.default(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 0, trimSpaces: true });
            if (streetNameMatch !== null)
                addresses.push({ houseNumber: houseNumber, streetName: streetName, suburbName: associatedSuburbName, threshold: 0, candidate: candidate });
            else {
                streetNameMatch = didyoumean2_1.default(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
                if (streetNameMatch !== null)
                    addresses.push({ houseNumber: houseNumber, streetName: streetNameMatch, suburbName: associatedSuburbName, threshold: 1, candidate: candidate });
                else {
                    streetNameMatch = didyoumean2_1.default(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true });
                    if (streetNameMatch !== null)
                        addresses.push({ houseNumber: houseNumber, streetName: streetNameMatch, suburbName: associatedSuburbName, threshold: 2, candidate: candidate });
                    else
                        addresses.push({ houseNumber: houseNumber, streetName: streetName, suburbName: associatedSuburbName, threshold: Number.MAX_VALUE, candidate: candidate }); // unrecognised street name
                }
            }
        }
    }
    if (addresses.length === 0)
        return undefined; // no valid addresses found
    // Sort the addresses so that "better" addresses are moved to the front of the array.
    addresses.sort(addressComparer);
    // Format and return the "best" address.
    let address = addresses[0];
    return formatAddress(address.houseNumber, address.streetName, address.suburbName);
}
// Returns a number indicating which address is "larger" (in this case "larger" means a "worse"
// address).  This can be used to sort addresses so that "better" addresses, ie. those with a
// house number and fewer spelling errors appear at the start of an array.
function addressComparer(a, b) {
    // As long as there are one or two spelling errors then prefer the address with a
    // house number (even if it has more spelling errors).
    if (a.threshold <= 2 && b.threshold <= 2) {
        if (a.houseNumber === "" && b.houseNumber !== "")
            return 1;
        else if (a.houseNumber !== "" && b.houseNumber === "")
            return -1;
    }
    // For larger numbers of spelling errors prefer addresses with fewer spelling errors before
    // considering the presence of a house number.
    if (a.threshold > b.threshold)
        return 1;
    else if (a.threshold < b.threshold)
        return -1;
    if (a.houseNumber === "" && b.houseNumber !== "")
        return 1;
    else if (a.houseNumber !== "" && b.houseNumber === "")
        return -1;
    // All other things being equal (as tested above), avoid addresses belonging to a candidate
    // that has an invalid hundred name.  This is because having an invalid hundred name often
    // means that the wrong delimiting space has been chosen for that candidate (as below where
    // candidate 0 contains the invalid hundred name, "BARUNGA View HD", and so likely the other
    // address in that candidate is also wrong, namely, "Lake Road").
    //
    // Where there are multiple candidates mark down the candidates that contain street names
    // ending in " HD" and so likely represent a hundred name, but do not actually contain a
    // valid hundred name.  For example, the valid street name "Lake View Road" in candidate 1
    // is the better choice in the following because the hundred name "BARUNGA View HD" in
    // candidate 0 is invalid.
    //
    //     BARUNGAüLake View HDüRoad
    //
    // Candidate 0: [BARUNGA] [Lake]   [View HD] [Road]
    //             └───╴Group 1╶────┘ └───╴Group 2╶────┘
    //     Resulting street names:
    //         BARUNGA View HD  <-- invalid hundred name
    //         Lake Road        <-- valid street name
    //
    // Candidate 1: [BARUNGA] [Lake View]   [HD] [Road]
    //             └──────╴Group 1╶──────┘ └─╴Group 2╶─┘
    //     Resulting street names:
    //         BARUNGA HD      <-- valid hundred name 
    //         Lake View Road  <-- valid street name
    if (a.candidate.hasInvalidHundredName && !b.candidate.hasInvalidHundredName)
        return 1;
    else if (!a.candidate.hasInvalidHundredName && b.candidate.hasInvalidHundredName)
        return -1;
}
// Parses the details from the elements associated with a single development application.
function parseApplicationElements(elements, startElement, informationUrl) {
    // Get the application number.
    let applicationNumber = getRightText(elements, "Application Number:", "Lodged Date:", "Description:");
    if (applicationNumber === undefined || applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    applicationNumber = applicationNumber.trim().replace(/\s[A-Z]*$/i, "").replace(/\s\s+/g, "").trim();
    console.log(`    Found \"${applicationNumber}\".`);
    // Get the description.
    let description = getRightText(elements, "Description:", undefined, "Applicant Name:");
    // Get the received date.
    let receivedDateText = getRightText(elements, "Lodged Date:", "Approval Date:", "Description:");
    let receivedDate = undefined;
    if (receivedDateText !== undefined)
        receivedDate = moment(receivedDateText.trim(), "D/MM/YYYY", true);
    // Get the address.
    let address = getRightText(elements, "Property Address", undefined, "Legal Description:");
    if (address === undefined || address.trim() === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because there is no address.  Elements: ${elementSummary}`);
        return undefined;
    }
    // Get the legal description.
    let legalDescription = getRightText(elements, "Legal Description:", undefined, undefined);
    // Construct the resulting application information.
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description !== undefined && description.trim() !== "") ? description : "No Description Provided"),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : "",
        legalDescription: (legalDescription === undefined) ? "" : legalDescription
    };
}
// Parses the development applications in the specified date range.
async function parsePdf(url) {
    console.log(`Reading development applications from ${url}.`);
    let developmentApplications = [];
    // Read the PDF.
    let buffer = await request({ url: url, encoding: null, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    // Parse the PDF.  Each page has the details of multiple applications.  Note that the PDF is
    // re-parsed on each iteration of the loop (ie. once for each page).  This then avoids large
    // memory usage by the PDF (just calling page._destroy() on each iteration of the loop appears
    // not to be enough to release all memory used by the PDF parsing).
    for (let pageIndex = 0; pageIndex < 500; pageIndex++) { // limit to an arbitrarily large number of pages (to avoid any chance of an infinite loop)
        let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
        if (pageIndex >= pdf.numPages)
            break;
        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);
        let textContent = await page.getTextContent();
        let viewport = await page.getViewport(1.0);
        let elements = textContent.items.map(item => {
            let transform = pdfjs.Util.transform(viewport.transform, item.transform);
            // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
            // exaggerated).  The problem seems to be that the height value is too large in some
            // PDFs.  Provide an alternative, more accurate height value by using a calculation
            // based on the transform matrix.
            let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);
            return { text: item.str, x: transform[4], y: transform[5], width: item.width, height: workaroundHeight };
        });
        // Release the memory used by the PDF now that it is no longer required (it will be
        // re-parsed on the next iteration of the loop for the next page).
        await pdf.destroy();
        if (global.gc)
            global.gc();
        // Sort the elements by Y co-ordinate and then by X co-ordinate.
        let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
        elements.sort(elementComparer);
        // Group the elements into sections based on where the "Application No" text starts.
        let applicationElementGroups = [];
        let startElements = findStartElements(elements);
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).  Allow some leeway vertically (add some extra height) because
            // in some cases the lodged date might be higher up than the "Application No" text.
            let startElement = startElements[index];
            let raisedStartElement = {
                text: startElement.text,
                x: startElement.x,
                y: startElement.y - startElement.height / 2,
                width: startElement.width,
                height: startElement.height
            };
            let rowTop = getRowTop(elements, raisedStartElement);
            let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;
            // Extract all elements between the two rows.
            applicationElementGroups.push({ startElement: startElements[index], elements: elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop) });
        }
        // Parse the development application from each group of elements (ie. a section of the
        // current page of the PDF document).  If the same application number is encountered a
        // second time in the same document then this likely indicates the parsing has incorrectly
        // recognised some of the digits in the application number.  In this case add a suffix to
        // the application number so it is unique (and so will be inserted into the database later
        // instead of being ignored).
        for (let applicationElementGroup of applicationElementGroups) {
            let developmentApplication = parseApplicationElements(applicationElementGroup.elements, applicationElementGroup.startElement, url);
            if (developmentApplication !== undefined) {
                let suffix = 0;
                let applicationNumber = developmentApplication.applicationNumber;
                while (developmentApplications.some(otherDevelopmentApplication => otherDevelopmentApplication.applicationNumber === developmentApplication.applicationNumber))
                    developmentApplication.applicationNumber = `${applicationNumber} (${++suffix})`; // add a unique suffix
                developmentApplications.push(developmentApplication);
            }
        }
    }
    return developmentApplications;
}
// Gets a random integer in the specified range: [minimum, maximum).
function getRandom(minimum, maximum) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}
// Pauses for the specified number of milliseconds.
function sleep(milliseconds) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}
// Parses the development applications.
async function main() {
    // Ensure that the database exists.
    let database = await initializeDatabase();
    // Read the files containing all possible street names, street suffixes, suburb names and
    // hundred names.
    StreetNames = {};
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.toUpperCase().split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        (StreetNames[streetName] || (StreetNames[streetName] = [])).push(suburbName); // several suburbs may exist for the same street name
    }
    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.toUpperCase().split(",");
        StreetSuffixes[streetSuffixTokens[0].trim()] = streetSuffixTokens[1].trim();
    }
    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.toUpperCase().split(",");
        SuburbNames[suburbTokens[0].trim()] = suburbTokens[1].trim();
    }
    HundredNames = [];
    for (let line of fs.readFileSync("hundrednames.txt").toString().replace(/\r/g, "").trim().split("\n"))
        HundredNames.push(line.trim().toUpperCase());
    // Read the main page of development applications.
    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);
    let body = await request({ url: DevelopmentApplicationsUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);
    let pdfUrls = [];
    for (let element of $("div.unityHtmlArticle ul li a").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl).href;
        if (pdfUrl.toLowerCase().includes("register") && pdfUrl.toLowerCase().includes(".pdf"))
            if (!pdfUrls.some(url => url === pdfUrl))
                pdfUrls.push(pdfUrl);
    }
    // Always parse the most recent PDF file and randomly select one other PDF file to parse.
    if (pdfUrls.length === 0) {
        console.log("No PDF files were found on the page.");
        return;
    }
    console.log(`Found ${pdfUrls.length} PDF file(s).  Selecting two to parse.`);
    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).
    let selectedPdfUrls = [];
    selectedPdfUrls.push(pdfUrls.pop());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(0, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();
    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl);
        console.log(`Parsed ${developmentApplications.length} development application(s) from document: ${pdfUrl}`);
        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).
        if (global.gc)
            global.gc();
        console.log(`Inserting development applications into the database.`);
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}
main().then(() => console.log("Complete.")).catch(error => console.error(error));
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2NyYXBlci5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbInNjcmFwZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsaUdBQWlHO0FBQ2pHLGlDQUFpQztBQUNqQyxFQUFFO0FBQ0YsZUFBZTtBQUNmLGtCQUFrQjtBQUVsQixZQUFZLENBQUM7O0FBRWIseUJBQXlCO0FBQ3pCLG1DQUFtQztBQUNuQyxrREFBa0Q7QUFDbEQsbUNBQW1DO0FBQ25DLGlDQUFpQztBQUNqQyxpQ0FBaUM7QUFDakMsb0NBQW9DO0FBQ3BDLHlFQUFzRDtBQUV0RCxPQUFPLENBQUMsT0FBTyxFQUFFLENBQUM7QUFFbEIsTUFBTSwwQkFBMEIsR0FBRyx1Q0FBdUMsQ0FBQztBQUMzRSxNQUFNLFVBQVUsR0FBRyxnQ0FBZ0MsQ0FBQztBQUlwRCwyRUFBMkU7QUFFM0UsSUFBSSxXQUFXLEdBQUcsSUFBSSxDQUFDO0FBQ3ZCLElBQUksY0FBYyxHQUFHLElBQUksQ0FBQztBQUMxQixJQUFJLFdBQVcsR0FBRyxJQUFJLENBQUM7QUFDdkIsSUFBSSxZQUFZLEdBQUcsSUFBSSxDQUFDO0FBRXhCLDhCQUE4QjtBQUU5QixLQUFLLFVBQVUsa0JBQWtCO0lBQzdCLE9BQU8sSUFBSSxPQUFPLENBQUMsQ0FBQyxPQUFPLEVBQUUsTUFBTSxFQUFFLEVBQUU7UUFDbkMsSUFBSSxRQUFRLEdBQUcsSUFBSSxPQUFPLENBQUMsUUFBUSxDQUFDLGFBQWEsQ0FBQyxDQUFDO1FBQ25ELFFBQVEsQ0FBQyxTQUFTLENBQUMsR0FBRyxFQUFFO1lBQ3BCLFFBQVEsQ0FBQyxHQUFHLENBQUMsd05BQXdOLENBQUMsQ0FBQztZQUN2TyxPQUFPLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDdEIsQ0FBQyxDQUFDLENBQUM7SUFDUCxDQUFDLENBQUMsQ0FBQztBQUNQLENBQUM7QUFFRCxtRUFBbUU7QUFFbkUsS0FBSyxVQUFVLFNBQVMsQ0FBQyxRQUFRLEVBQUUsc0JBQXNCO0lBQ3JELE9BQU8sSUFBSSxPQUFP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