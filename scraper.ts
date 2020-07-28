// Parses the development applications at the South Australian District Council of Cleve web site
// and places them in a database.
//
// Michael Bone
// 17th March 2019

"use strict";

import * as fs from "fs";
import * as cheerio from "cheerio";
import * as request from "request-promise-native";
import * as sqlite3 from "sqlite3";
import * as urlparser from "url";
import * as moment from "moment";
import * as pdfjs from "pdfjs-dist";
import didYouMean, * as didyoumean from "didyoumean2";

sqlite3.verbose();

const DevelopmentApplicationsUrl = "https://www.cleve.sa.gov.au/council/documents/registers";
const CommentUrl = "mailto:council@cleve.sa.gov.au";

const Tolerance = 3;

declare const process: any;

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
        let sqlStatement = database.prepare("insert or replace into [data] values (?, ?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate,
            developmentApplication.legalDescription
        ], function(error, row) {
            if (error) {
                console.error(error);
                reject(error);
            } else {
                console.log(`    Saved application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\", legal description \"${developmentApplication.legalDescription}\" and received date \"${developmentApplication.receivedDate}\" to the database.`);
                sqlStatement.finalize();  // releases any locks
                resolve(row);
            }
        });
    });
}

// A bounding rectangle.

interface Rectangle {
    x: number,
    y: number,
    width: number,
    height: number
}

// An element (consisting of text and a bounding rectangle) in a PDF document.

interface Element extends Rectangle {
    text: string
}

// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.  Take care to avoid extremely tall elements (because these may otherwise
// be considered as part of all rows and effectively force the return value of this function to
// the same value, regardless of the value of startElement).

function getRowTop(elements: Element[], startElement: Element) {
    let top = startElement.y;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y)  // check for overlap
            if (getVerticalOverlapPercentage(startElement, element) > 50)  // avoids extremely tall elements
                if (element.y < top)
                    top = element.y;
    return top;
}

// Constructs a rectangle based on the union of the two specified rectangles.

function union(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x = Math.min(rectangle1.x, rectangle2.x);
    let y = Math.min(rectangle1.y, rectangle1.y);
    let width = Math.max(Math.max(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width) - x, 0);
    let height = Math.max(Math.max(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height) - y, 0);
    return { x: x, y: y, width: width, height: height };
}

// Constructs a rectangle based on the intersection of the two specified rectangles.

function intersect(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}

// Calculates the fraction of an element that lies within a rectangle (as a percentage).  For
// example, if a quarter of the specifed element lies within the specified rectangle then this
// would return 25.

function getPercentageOfElementInRectangle(element: Element, rectangle: Rectangle) {
    let elementArea = getArea(element);
    let intersectionArea = getArea(intersect(rectangle, element));
    return (elementArea === 0) ? 0 : ((intersectionArea * 100) / elementArea);
}

// Calculates the area of a rectangle.

function getArea(rectangle: Rectangle) {
    return rectangle.width * rectangle.height;
}

// Calculates the square of the Euclidean distance between two elements.

function calculateDistance(element1: Element, element2: Element) {
    let point1 = { x: element1.x + element1.width, y: element1.y + element1.height / 2 };
    let point2 = { x: element2.x, y: element2.y + element2.height / 2 };
    if (point2.x < point1.x - element1.width / 5)  // arbitrary overlap factor of 20% (ie. ignore elements that overlap too much in the horizontal direction)
        return Number.MAX_VALUE;
    return (point2.x - point1.x) * (point2.x - point1.x) + (point2.y - point1.y) * (point2.y - point1.y);
}

// Determines whether there is vertical overlap between two elements.

function isVerticalOverlap(element1: Element, element2: Element) {
    return element2.y < element1.y + element1.height && element2.y + element2.height > element1.y;
}

// Gets the percentage of vertical overlap between two elements (0 means no overlap and 100 means
// 100% overlap; and, for example, 20 means that 20% of the second element overlaps somewhere
// with the first element).

function getVerticalOverlapPercentage(element1: Element, element2: Element) {
    let y1 = Math.max(element1.y, element2.y);
    let y2 = Math.min(element1.y + element1.height, element2.y + element2.height);
    return (y2 < y1) ? 0 : (((y2 - y1) * 100) / element2.height);
}

// Gets the element immediately to the right of the specified element (but ignores elements that
// appear after a large horizontal gap).

function getRightElement(elements: Element[], element: Element) {
    let closestElement: Element = { text: undefined, x: Number.MAX_VALUE, y: Number.MAX_VALUE, width: 0, height: 0 };
    for (let rightElement of elements)
        if (isVerticalOverlap(element, rightElement) &&  // ensure that there is at least some vertical overlap
            getVerticalOverlapPercentage(element, rightElement) > 50 &&  // avoid extremely tall elements (ensure at least 50% overlap)
            (rightElement.x > element.x + element.width - Tolerance) &&  // ensure the element actually is to the right (approximately)
            (rightElement.x - (element.x + element.width) < 30) &&  // avoid elements that appear after a large gap (arbitrarily ensure less than a 30 pixel gap horizontally)
            calculateDistance(element, rightElement) < calculateDistance(element, closestElement))  // check if closer than any element encountered so far
            closestElement = rightElement;
    return (closestElement.text === undefined) ? undefined : closestElement;
}

// Finds the elements that most closely match the specified text and returns a rectangle that
// encompasses all of those elements.

function findTextBounds(elements: Element[], text: string) {
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
        let rightElements: Element[] = [];

        do {
            rightElements.push(rightElement);

            let currentText = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();

            if (currentText.length > condensedText.length + 2)  // stop once the text is too long
                break;
            if (currentText.length >= condensedText.length - 2) {  // ignore until the text is close to long enough
                if (currentText === condensedText)
                    matches.push({ elements: [...rightElements], threshold: 0, text: currentText });
                else if (didYouMean(currentText, [ condensedText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ elements: [...rightElements], threshold: 1, text: currentText });
                else if (didYouMean(currentText, [ condensedText ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ elements: [...rightElements], threshold: 2, text: currentText });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5);  // up to 5 elements
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
        let bestMatch = matches.reduce((previous, current) =>
            (previous === undefined ||
            current.threshold < previous.threshold ||
            (current.threshold === previous.threshold && Math.abs(current.text.trim().length - condensedText.length) < Math.abs(previous.text.trim().length - condensedText.length)) ? current : previous), undefined);

        // Union together the rectangles of all elements belonging to the best match.

        let rectangle = undefined;
        for (let element of bestMatch.elements)
            rectangle = (rectangle === undefined) ? element : union(rectangle, element);
        return { x: rectangle.x, y: rectangle.y, width: rectangle.width, height: rectangle.height };
    }

    return undefined;
}

// Finds the start element of each development application on the current PDF page (there are
// typically two development applications on a single page and each development application
// typically begins with the text "Application Number").

function findStartElements(elements: Element[]) {
    // Examine all the elements on the page that being with "A" or "a".
    
    let startElements: Element[] = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith("a"))) {
        // Extract up to 5 elements to the right of the element that has text starting with
        // the letter "a" (and so may be the start of the "Application Number" text).  Join
        // together the elements to the right in an attempt to find the best match to the text
        // "Application Number".

        let rightElement = element;
        let rightElements: Element[] = [];
        let matches = [];

        do {
            rightElements.push(rightElement);
        
            // Allow for common misspellings of the "no." text.

            let text = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();
            if (text.length >= 20)  // stop once the text is too long
                break;
            if (text.length >= 17) {  // ignore until the text is close to long enough
                if (text === "applicationnumber")
                    matches.push({ element: rightElement, threshold: 0, text: text });
                else if (didYouMean(text, [ "ApplicationNumber" ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 1, text: text });
                else if (didYouMean(text, [ "ApplicationNumber" ], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 2, text: text });
            }

            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5);  // up to 5 elements

        // Chose the best match (if any matches were found).

        if (matches.length > 0) {
            let bestMatch = matches.reduce((previous, current) =>
                (previous === undefined ||
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

// Parses the details from the elements associated with a single development application.

function parseApplicationElements(elements: Element[], informationUrl: string) {
    let applicationNumberHeadingBounds = findTextBounds(elements, "Application Number");
    let lodgedDateHeadingBounds = findTextBounds(elements, "Lodged Date");
    let approvalDateHeadingBounds = findTextBounds(elements, "Approval Date");
    let descriptionHeadingBounds = findTextBounds(elements, "Description");
    let propertyAddressHeadingBounds = findTextBounds(elements, "Property Address");
    let legalDescriptionHeadingBounds = findTextBounds(elements, "Legal Description");

    // Get the application number.

    if (applicationNumberHeadingBounds === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the "Application Number" heading on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    let applicationNumberBounds = {
        x: applicationNumberHeadingBounds.x + applicationNumberHeadingBounds.width,
        y: applicationNumberHeadingBounds.y,
        width: (lodgedDateHeadingBounds === undefined) ? 2 * applicationNumberHeadingBounds.width : (lodgedDateHeadingBounds.x - applicationNumberHeadingBounds.x - applicationNumberHeadingBounds.width),
        height: applicationNumberHeadingBounds.height
    };
    let applicationNumber = elements.filter(element => getPercentageOfElementInRectangle(element, applicationNumberBounds) > 10).map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
    if (applicationNumber === undefined || applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    applicationNumber = applicationNumber.trim().replace(/\s[A-Z]*$/i, "").replace(/\s/g, "").trim();
    console.log(`    Found \"${applicationNumber}\".`);

    // Get the received date.

    let receivedDate: moment.Moment = undefined;
    if (lodgedDateHeadingBounds !== undefined) {
        let receivedDateBounds = {
            x: lodgedDateHeadingBounds.x + lodgedDateHeadingBounds.width,
            y: lodgedDateHeadingBounds.y,
            width: (approvalDateHeadingBounds === undefined) ? 2 * lodgedDateHeadingBounds.width : (approvalDateHeadingBounds.x - lodgedDateHeadingBounds.x - lodgedDateHeadingBounds.width),
            height: lodgedDateHeadingBounds.height
        };
        let receivedDateText = elements.filter(element => getPercentageOfElementInRectangle(element, receivedDateBounds) > 10).map(element => element.text).join("").trim().replace(/\s\s+/g, " ");
        if (receivedDateText !== undefined)
            receivedDate = moment(receivedDateText.trim().substring(0, 10), "D/MM/YYYY", true);
    }

    // Get the description.

    let description = "";
    if (descriptionHeadingBounds !== undefined) {
        let descriptionBounds = {
            x: descriptionHeadingBounds.x + descriptionHeadingBounds.width,
            y: descriptionHeadingBounds.y,
            width: Number.MAX_VALUE,
            height: descriptionHeadingBounds.height
        };
        description = elements.filter(element => getPercentageOfElementInRectangle(element, descriptionBounds) > 10).map(element => element.text).join("").trim().replace(/\s\s+/g, " ");
    }

    // Get the address.

    if (propertyAddressHeadingBounds === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the "Property Address" heading on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    let addressBounds = {
        x: propertyAddressHeadingBounds.x + propertyAddressHeadingBounds.width,
        y: propertyAddressHeadingBounds.y,
        width: Number.MAX_VALUE,
        height: (legalDescriptionHeadingBounds === undefined) ? Number.MAX_VALUE : (legalDescriptionHeadingBounds.y - propertyAddressHeadingBounds.y)
    };
    let addressElements = elements.filter(element => getPercentageOfElementInRectangle(element, addressBounds) > 10);
    
    let addressText = addressElements.map(element => element.text).join("").trim().replace(/\s\s+/g, " ");
    if (addressText === undefined || addressText.trim() === "")
    {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because there is no address.  Elements: ${elementSummary}`);
        return undefined;
    }

    // Group the address elements into rows.

    let addressRows: Element[][] = [];
    for (let addressElement of addressElements) {
        let addressRow = addressRows.find(row => Math.abs(row[0].y - addressElement.y) < 2 * Tolerance);  // approximate Y co-ordinate match
        if (addressRow === undefined)
            addressRows.push([ addressElement ]);  // start a new row
        else
            addressRow.push(addressElement);  // add to an existing row
    }

    let addressLines = addressRows.map(addressRow => addressRow.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " "));
    let address = addressLines.filter(line => line !== "").join(", ");  // ignore blank lines

    // Get the legal description.

    let legalDescription = "";
    if (legalDescriptionHeadingBounds !== undefined) {
        let legalDescriptionBounds = {
            x: legalDescriptionHeadingBounds.x + legalDescriptionHeadingBounds.width,
            y: legalDescriptionHeadingBounds.y,
            width: Number.MAX_VALUE,
            height: Number.MAX_VALUE
        };
        let legalDescriptionElements = elements.filter(element => getPercentageOfElementInRectangle(element, legalDescriptionBounds) > 10);

        // Group the legal description elements into rows.

        let legalDescriptionRows: Element[][] = [];
        for (let legalDescriptionElement of legalDescriptionElements) {
            let legalDescriptionRow = legalDescriptionRows.find(row => Math.abs(row[0].y - legalDescriptionElement.y) < 2 * Tolerance);  // approximate Y co-ordinate match
            if (legalDescriptionRow === undefined)
                legalDescriptionRows.push([ legalDescriptionElement ]);  // start a new row
            else
                legalDescriptionRow.push(legalDescriptionElement);  // add to an existing row
        }

        let legalDescriptionLines = legalDescriptionRows.map(legalDescriptionRow => legalDescriptionRow.map(element => element.text).join("").trim().replace(/\s\s+/g, " "));
        legalDescription = legalDescriptionLines.filter(line => line !== "").join(", ");  // ignore blank lines
    }

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

async function parsePdf(url: string) {
    console.log(`Reading development applications from ${url}.`);

    let developmentApplications = [];

    // Read the PDF.

    let buffer = await request({ url: url, encoding: null, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);

    // Parse the PDF.  Each page has the details of multiple applications.  Note that the PDF is
    // re-parsed on each iteration of the loop (ie. once for each page).  This then avoids large
    // memory usage by the PDF (just calling page._destroy() on each iteration of the loop appears
    // not to be enough to release all memory used by the PDF parsing).

    for (let pageIndex = 0; pageIndex < 500; pageIndex++) {  // limit to an arbitrarily large number of pages (to avoid any chance of an infinite loop)
        let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
        if (pageIndex >= pdf.numPages)
            break;

        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);
        let textContent = await page.getTextContent();
        let viewport = await page.getViewport(1.0);
    
        let elements: Element[] = textContent.items.map(item => {
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

        // Sort the elements by approximate Y co-ordinate and then by X co-ordinate.

        let elementComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        elements.sort(elementComparer);

        // Group the elements into sections based on where the "Application No" text starts.

        let applicationElementGroups = [];
        let startElements = findStartElements(elements);
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).  Allow some leeway vertically (add some extra height) because
            // in some cases the lodged date might be higher up than the "Application No" text.
            
            let startElement = startElements[index];
            let raisedStartElement: Element = {
                text: startElement.text,
                x: startElement.x,
                y: startElement.y - startElement.height / 2,  // leeway
                width: startElement.width,
                height: startElement.height };
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
            let developmentApplication = parseApplicationElements(applicationElementGroup.elements, url);
            if (developmentApplication !== undefined) {
                let suffix = 0;
                let applicationNumber = developmentApplication.applicationNumber;
                while (developmentApplications.some(otherDevelopmentApplication => otherDevelopmentApplication.applicationNumber === developmentApplication.applicationNumber))
                    developmentApplication.applicationNumber = `${applicationNumber} (${++suffix})`;  // add a unique suffix
                developmentApplications.push(developmentApplication);
            }
        }
    }

    return developmentApplications;
}

// Gets a random integer in the specified range: [minimum, maximum).

function getRandom(minimum: number, maximum: number) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}

// Pauses for the specified number of milliseconds.

function sleep(milliseconds: number) {
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
        (StreetNames[streetName] || (StreetNames[streetName] = [])).push(suburbName);  // several suburbs may exist for the same street name
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

    let pdfUrls: string[] = [];
    for (let element of $("div.unityHtmlArticle ul li a").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl).href
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

    let selectedPdfUrls: string[] = [];
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
